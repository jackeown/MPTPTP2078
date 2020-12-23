%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m16WKykivB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  375 ( 759 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(t5_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( m1_subset_1 @ ( k1_yellow19 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X3 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow19])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t4_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
             => ( ( r2_waybel_7 @ A @ C @ B )
              <=> ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_yellow19 @ X8 @ X7 ) @ X9 )
      | ( r2_waybel_7 @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X8 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ ( k2_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow19])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) )
        & ( v1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
        & ( v2_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
        & ( v13_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v13_waybel_0 @ ( k1_yellow19 @ X5 @ X6 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow19])).

thf('17',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m16WKykivB
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 20 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.47  thf(t5_yellow19, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t5_yellow19])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k1_yellow19, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.47         ( k1_zfmisc_1 @
% 0.21/0.47           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X3)
% 0.21/0.47          | ~ (v2_pre_topc @ X3)
% 0.21/0.47          | (v2_struct_0 @ X3)
% 0.21/0.47          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.47          | (m1_subset_1 @ (k1_yellow19 @ X3 @ X4) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X3))))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_yellow19])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.47  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t4_yellow19, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47                 ( m1_subset_1 @
% 0.21/0.47                   C @ 
% 0.21/0.47                   ( k1_zfmisc_1 @
% 0.21/0.47                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.47               ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 0.21/0.47                 ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.47          | ~ (r1_tarski @ (k1_yellow19 @ X8 @ X7) @ X9)
% 0.21/0.47          | (r2_waybel_7 @ X8 @ X9 @ X7)
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X8)))))
% 0.21/0.47          | ~ (v13_waybel_0 @ X9 @ (k3_yellow_1 @ (k2_struct_0 @ X8)))
% 0.21/0.47          | ~ (l1_pre_topc @ X8)
% 0.21/0.47          | ~ (v2_pre_topc @ X8)
% 0.21/0.47          | (v2_struct_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_yellow19])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.47          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 0.21/0.47          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.47               (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(fc1_yellow19, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( ( ~( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) ) ) & 
% 0.21/0.47         ( v1_subset_1 @
% 0.21/0.47           ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.47           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.47         ( v2_waybel_0 @
% 0.21/0.47           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47         ( v13_waybel_0 @
% 0.21/0.47           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X5)
% 0.21/0.47          | ~ (v2_pre_topc @ X5)
% 0.21/0.47          | (v2_struct_0 @ X5)
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.47          | (v13_waybel_0 @ (k1_yellow19 @ X5 @ X6) @ 
% 0.21/0.47             (k3_yellow_1 @ (k2_struct_0 @ X5))))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_yellow19])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.47  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 0.21/0.47          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.47               (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13', '14', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '23'])).
% 0.21/0.47  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (~ (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
