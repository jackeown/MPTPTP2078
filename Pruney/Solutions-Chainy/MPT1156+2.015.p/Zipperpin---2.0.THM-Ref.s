%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2KWdKE9kh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  383 ( 823 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X10 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ ( k2_orders_2 @ X20 @ X21 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f2KWdKE9kh
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 16:52:36 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 134 iterations in 0.067s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.56  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.38/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.56  thf(t50_orders_2, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.38/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56           ( ~( r2_hidden @
% 0.38/0.56                B @ 
% 0.38/0.56                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.38/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56              ( ~( r2_hidden @
% 0.38/0.56                   B @ 
% 0.38/0.56                   ( k2_orders_2 @
% 0.38/0.56                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t50_orders_2])).
% 0.38/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X17)
% 0.38/0.56          | ~ (m1_subset_1 @ X18 @ X17)
% 0.38/0.56          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((r2_hidden @ sk_B @ 
% 0.38/0.56        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d2_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X7 @ X8)
% 0.38/0.56          | (r2_hidden @ X7 @ X8)
% 0.38/0.56          | (v1_xboole_0 @ X8))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf(t63_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k1_tarski @ X10) @ (k1_zfmisc_1 @ X11))
% 0.38/0.56          | ~ (r2_hidden @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(t49_orders_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.38/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56               ( ~( ( r2_hidden @ B @ C ) & 
% 0.38/0.56                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.38/0.56          | ~ (r2_hidden @ X19 @ (k2_orders_2 @ X20 @ X21))
% 0.38/0.56          | ~ (r2_hidden @ X19 @ X21)
% 0.38/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.56          | ~ (l1_orders_2 @ X20)
% 0.38/0.56          | ~ (v5_orders_2 @ X20)
% 0.38/0.56          | ~ (v4_orders_2 @ X20)
% 0.38/0.56          | ~ (v3_orders_2 @ X20)
% 0.38/0.56          | (v2_struct_0 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56          | (v2_struct_0 @ sk_A)
% 0.38/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.38/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.38/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.38/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56          | (v2_struct_0 @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.38/0.56        | (v2_struct_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '17'])).
% 0.38/0.56  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t69_enumset1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.56  thf('20', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.56  thf(d2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((X1) != (X0))
% 0.38/0.56          | (r2_hidden @ X1 @ X2)
% 0.38/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.56  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['20', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (v2_struct_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['18', '19', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.56  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf(fc2_struct_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X15 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.38/0.56          | ~ (l1_struct_0 @ X15)
% 0.38/0.56          | (v2_struct_0 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.56  thf('29', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_l1_orders_2, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.38/0.56  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '32'])).
% 0.38/0.56  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
