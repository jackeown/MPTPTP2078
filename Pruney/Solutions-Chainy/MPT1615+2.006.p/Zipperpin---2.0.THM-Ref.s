%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SHuvqv4CrM

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 ( 298 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

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
    ! [X4: $i] :
      ( ( ( k3_yellow_0 @ X4 )
        = ( k1_yellow_0 @ X4 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X10 ) ) ) ) )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X10 ) ) @ X9 )
        = ( k3_tarski @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X10 ) ) )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X10 ) ) @ X9 )
        = ( k3_tarski @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 )
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SHuvqv4CrM
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 17 iterations in 0.011s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.22/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.45  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.45  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.22/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.45  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.45  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.45  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.45  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.22/0.45  thf(t23_yellow_1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.45       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.22/0.45         ( k1_xboole_0 ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.45            ( l1_pre_topc @ A ) ) =>
% 0.22/0.45          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.22/0.45            ( k1_xboole_0 ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.22/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(d11_yellow_0, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( l1_orders_2 @ A ) =>
% 0.22/0.45       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X4 : $i]:
% 0.22/0.45         (((k3_yellow_0 @ X4) = (k1_yellow_0 @ X4 @ k1_xboole_0))
% 0.22/0.45          | ~ (l1_orders_2 @ X4))),
% 0.22/0.45      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.22/0.45  thf(t4_subset_1, axiom,
% 0.22/0.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.45  thf(t22_yellow_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( m1_subset_1 @
% 0.22/0.45             B @ 
% 0.22/0.45             ( k1_zfmisc_1 @
% 0.22/0.45               ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 0.22/0.45           ( ( k1_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) @ B ) =
% 0.22/0.45             ( k3_tarski @ B ) ) ) ) ))).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X9 : $i, X10 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X9 @ 
% 0.22/0.45             (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ X10)))))
% 0.22/0.45          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X10)) @ X9)
% 0.22/0.45              = (k3_tarski @ X9))
% 0.22/0.45          | ~ (l1_pre_topc @ X10)
% 0.22/0.45          | ~ (v2_pre_topc @ X10)
% 0.22/0.45          | (v2_struct_0 @ X10))),
% 0.22/0.45      inference('cnf', [status(esa)], [t22_yellow_1])).
% 0.22/0.45  thf(t1_yellow_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.22/0.45       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.45  thf('4', plain, (![X7 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X7)) = (X7))),
% 0.22/0.45      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X9 : $i, X10 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_pre_topc @ X10)))
% 0.22/0.45          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X10)) @ X9)
% 0.22/0.45              = (k3_tarski @ X9))
% 0.22/0.45          | ~ (l1_pre_topc @ X10)
% 0.22/0.45          | ~ (v2_pre_topc @ X10)
% 0.22/0.45          | (v2_struct_0 @ X10))),
% 0.22/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((v2_struct_0 @ X0)
% 0.22/0.45          | ~ (v2_pre_topc @ X0)
% 0.22/0.45          | ~ (l1_pre_topc @ X0)
% 0.22/0.45          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)) @ k1_xboole_0)
% 0.22/0.45              = (k3_tarski @ k1_xboole_0)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.45  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.45  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.45      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         ((v2_struct_0 @ X0)
% 0.22/0.45          | ~ (v2_pre_topc @ X0)
% 0.22/0.45          | ~ (l1_pre_topc @ X0)
% 0.22/0.45          | ((k1_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)) @ k1_xboole_0)
% 0.22/0.45              = (k1_xboole_0)))),
% 0.22/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0))
% 0.22/0.45          | ~ (l1_orders_2 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.22/0.45          | ~ (l1_pre_topc @ X0)
% 0.22/0.45          | ~ (v2_pre_topc @ X0)
% 0.22/0.45          | (v2_struct_0 @ X0))),
% 0.22/0.45      inference('sup+', [status(thm)], ['1', '8'])).
% 0.22/0.45  thf(dt_k2_yellow_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.22/0.45       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.22/0.45  thf('10', plain, (![X6 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X6))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0))
% 0.22/0.45          | ~ (l1_pre_topc @ X0)
% 0.22/0.45          | ~ (v2_pre_topc @ X0)
% 0.22/0.45          | (v2_struct_0 @ X0))),
% 0.22/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.45  thf('12', plain,
% 0.22/0.45      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('13', plain,
% 0.22/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.45        | (v2_struct_0 @ sk_A)
% 0.22/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.45        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.45  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('16', plain, ((((k1_xboole_0) != (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.22/0.45      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.45  thf('17', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.45      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.45  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
