%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pyW8YeiU9Y

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   58 (  64 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  294 ( 366 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t23_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( ( k3_yellow_0 @ X12 )
        = ( k1_yellow_0 @ X12 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) )
         => ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B )
            = ( k3_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X18 ) ) ) ) )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X18 ) ) @ X17 )
        = ( k3_tarski @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X18 ) ) )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X18 ) ) @ X17 )
        = ( k3_tarski @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 )
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('14',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pyW8YeiU9Y
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:04:44 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 27 iterations in 0.017s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.23/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.49  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.23/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.23/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.23/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.23/0.50  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(t23_yellow_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.50       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.23/0.50         ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.50            ( l1_pre_topc @ A ) ) =>
% 0.23/0.50          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.23/0.50            ( k1_xboole_0 ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.23/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d11_yellow_0, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_orders_2 @ A ) =>
% 0.23/0.50       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X12 : $i]:
% 0.23/0.50         (((k3_yellow_0 @ X12) = (k1_yellow_0 @ X12 @ k1_xboole_0))
% 0.23/0.50          | ~ (l1_orders_2 @ X12))),
% 0.23/0.50      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.23/0.50  thf(t4_subset_1, axiom,
% 0.23/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.50  thf(t22_yellow_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @
% 0.23/0.50             B @ 
% 0.23/0.50             ( k1_zfmisc_1 @
% 0.23/0.50               ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 0.23/0.50           ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B ) =
% 0.23/0.50             ( k3_tarski @ B ) ) ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X17 : $i, X18 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X17 @ 
% 0.23/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X18)))))
% 0.23/0.50          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X18)) @ X17)
% 0.23/0.50              = (k3_tarski @ X17))
% 0.23/0.50          | ~ (l1_pre_topc @ X18)
% 0.23/0.50          | ~ (v2_pre_topc @ X18)
% 0.23/0.50          | (v2_struct_0 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [t22_yellow_1])).
% 0.23/0.50  thf(t1_yellow_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.23/0.50       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.50  thf('4', plain, (![X15 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X15)) = (X15))),
% 0.23/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X17 : $i, X18 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_pre_topc @ X18)))
% 0.23/0.50          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X18)) @ X17)
% 0.23/0.50              = (k3_tarski @ X17))
% 0.23/0.50          | ~ (l1_pre_topc @ X18)
% 0.23/0.50          | ~ (v2_pre_topc @ X18)
% 0.23/0.50          | (v2_struct_0 @ X18))),
% 0.23/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((v2_struct_0 @ X0)
% 0.23/0.50          | ~ (v2_pre_topc @ X0)
% 0.23/0.50          | ~ (l1_pre_topc @ X0)
% 0.23/0.50          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)) @ k1_xboole_0)
% 0.23/0.50              = (k3_tarski @ k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.50  thf(t94_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.23/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.23/0.50          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.23/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.23/0.50  thf(t113_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X2 : $i, X3 : $i]:
% 0.23/0.50         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.50  thf(t152_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.23/0.50  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf('12', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '11'])).
% 0.23/0.50  thf(t3_xboole_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.23/0.50  thf('14', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((v2_struct_0 @ X0)
% 0.23/0.50          | ~ (v2_pre_topc @ X0)
% 0.23/0.50          | ~ (l1_pre_topc @ X0)
% 0.23/0.50          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)) @ k1_xboole_0)
% 0.23/0.50              = (k1_xboole_0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['6', '14'])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0))
% 0.23/0.50          | ~ (l1_orders_2 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.23/0.50          | ~ (l1_pre_topc @ X0)
% 0.23/0.50          | ~ (v2_pre_topc @ X0)
% 0.23/0.50          | (v2_struct_0 @ X0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['1', '15'])).
% 0.23/0.50  thf(dt_k2_yellow_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.23/0.50       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.23/0.50  thf('17', plain, (![X14 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X14))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0))
% 0.23/0.50          | ~ (l1_pre_topc @ X0)
% 0.23/0.50          | ~ (v2_pre_topc @ X0)
% 0.23/0.50          | (v2_struct_0 @ X0))),
% 0.23/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50        | (v2_struct_0 @ sk_A)
% 0.23/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('23', plain, ((((k1_xboole_0) != (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.23/0.50  thf('24', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.50  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
