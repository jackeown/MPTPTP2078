%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wiV2PaCK6E

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  431 ( 829 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( v1_subset_1 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( k1_yellow19 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X6 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow19])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_tarski @ ( k1_yellow19 @ X11 @ X10 ) @ X12 )
      | ( r2_waybel_7 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X11 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow19])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( v13_waybel_0 @ ( k1_yellow19 @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow19])).

thf('24',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','29'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wiV2PaCK6E
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 38 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(t5_yellow19, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t5_yellow19])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(rc3_subset_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ?[B:$i]:
% 0.21/0.48       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('3', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.48  thf(d7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (((X5) = (X4))
% 0.21/0.48          | (v1_subset_1 @ X5 @ X4)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, (![X0 : $i]: ~ (v1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.48  thf('8', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k1_yellow19, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.48         ( k1_zfmisc_1 @
% 0.21/0.48           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X6)
% 0.21/0.48          | ~ (v2_pre_topc @ X6)
% 0.21/0.48          | (v2_struct_0 @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.21/0.48          | (m1_subset_1 @ (k1_yellow19 @ X6 @ X7) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X6))))))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_yellow19])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.48  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf(t4_yellow19, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48                 ( m1_subset_1 @
% 0.21/0.48                   C @ 
% 0.21/0.48                   ( k1_zfmisc_1 @
% 0.21/0.48                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48               ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 0.21/0.48                 ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ X11 @ X10) @ X12)
% 0.21/0.48          | (r2_waybel_7 @ X11 @ X12 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X11)))))
% 0.21/0.48          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ X11)))
% 0.21/0.48          | ~ (l1_pre_topc @ X11)
% 0.21/0.48          | ~ (v2_pre_topc @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_yellow19])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.48               (k1_yellow19 @ sk_A @ sk_B_1))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(fc1_yellow19, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( ~( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) ) ) & 
% 0.21/0.48         ( v1_subset_1 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.48           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.48         ( v2_waybel_0 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48         ( v13_waybel_0 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X8)
% 0.21/0.48          | ~ (v2_pre_topc @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.48          | (v13_waybel_0 @ (k1_yellow19 @ X8 @ X9) @ 
% 0.21/0.48             (k3_yellow_1 @ (k2_struct_0 @ X8))))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_yellow19])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.48  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B_1) @ 
% 0.21/0.48        (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.48               (k1_yellow19 @ sk_A @ sk_B_1))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '30'])).
% 0.21/0.48  thf('32', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (~ (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
