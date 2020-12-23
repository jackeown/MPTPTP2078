%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r9j6fU73ma

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:54 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  406 ( 625 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X7 @ X6 ) @ X8 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','19','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r9j6fU73ma
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.33/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.33/1.51  % Solved by: fo/fo7.sh
% 1.33/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.51  % done 1235 iterations in 1.042s
% 1.33/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.33/1.51  % SZS output start Refutation
% 1.33/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.33/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.33/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.33/1.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.33/1.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.33/1.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.33/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.33/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.33/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.51  thf(t44_tops_1, conjecture,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( l1_pre_topc @ A ) =>
% 1.33/1.51       ( ![B:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.33/1.51           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.33/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.51    (~( ![A:$i]:
% 1.33/1.51        ( ( l1_pre_topc @ A ) =>
% 1.33/1.51          ( ![B:$i]:
% 1.33/1.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.33/1.51              ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ) )),
% 1.33/1.51    inference('cnf.neg', [status(esa)], [t44_tops_1])).
% 1.33/1.51  thf('0', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(t36_xboole_1, axiom,
% 1.33/1.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.33/1.51  thf('1', plain,
% 1.33/1.51      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 1.33/1.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.33/1.51  thf(t3_subset, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.33/1.51  thf('2', plain,
% 1.33/1.51      (![X9 : $i, X11 : $i]:
% 1.33/1.51         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 1.33/1.51      inference('cnf', [status(esa)], [t3_subset])).
% 1.33/1.51  thf('3', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.33/1.51      inference('sup-', [status(thm)], ['1', '2'])).
% 1.33/1.51  thf(t48_pre_topc, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( l1_pre_topc @ A ) =>
% 1.33/1.51       ( ![B:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.33/1.51           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 1.33/1.51  thf('4', plain,
% 1.33/1.51      (![X14 : $i, X15 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.33/1.51          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 1.33/1.51          | ~ (l1_pre_topc @ X15))),
% 1.33/1.51      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.33/1.51  thf('5', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         (~ (l1_pre_topc @ X0)
% 1.33/1.51          | (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 1.33/1.51             (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['3', '4'])).
% 1.33/1.51  thf('6', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(d5_subset_1, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.33/1.51  thf('7', plain,
% 1.33/1.51      (![X4 : $i, X5 : $i]:
% 1.33/1.51         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 1.33/1.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 1.33/1.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.33/1.51  thf('8', plain,
% 1.33/1.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.33/1.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.33/1.51      inference('sup-', [status(thm)], ['6', '7'])).
% 1.33/1.51  thf('9', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.33/1.51      inference('sup-', [status(thm)], ['1', '2'])).
% 1.33/1.51  thf(dt_k2_pre_topc, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( ( l1_pre_topc @ A ) & 
% 1.33/1.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.33/1.51       ( m1_subset_1 @
% 1.33/1.51         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.33/1.51  thf('10', plain,
% 1.33/1.51      (![X12 : $i, X13 : $i]:
% 1.33/1.51         (~ (l1_pre_topc @ X12)
% 1.33/1.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.33/1.51          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 1.33/1.51             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 1.33/1.51      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.33/1.51  thf('11', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         ((m1_subset_1 @ 
% 1.33/1.51           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 1.33/1.51           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.33/1.51          | ~ (l1_pre_topc @ X0))),
% 1.33/1.51      inference('sup-', [status(thm)], ['9', '10'])).
% 1.33/1.51  thf(t36_subset_1, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.51       ( ![C:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.51           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 1.33/1.51             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 1.33/1.51  thf('12', plain,
% 1.33/1.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.33/1.51          | (r1_tarski @ (k3_subset_1 @ X7 @ X6) @ X8)
% 1.33/1.51          | ~ (r1_tarski @ (k3_subset_1 @ X7 @ X8) @ X6)
% 1.33/1.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.33/1.51      inference('cnf', [status(esa)], [t36_subset_1])).
% 1.33/1.51  thf('13', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.33/1.51         (~ (l1_pre_topc @ X0)
% 1.33/1.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.33/1.51          | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X2) @ 
% 1.33/1.51               (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))
% 1.33/1.51          | (r1_tarski @ 
% 1.33/1.51             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.33/1.51              (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))) @ 
% 1.33/1.51             X2))),
% 1.33/1.51      inference('sup-', [status(thm)], ['11', '12'])).
% 1.33/1.51  thf('14', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.33/1.51             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))
% 1.33/1.51          | (r1_tarski @ 
% 1.33/1.51             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 1.33/1.51             sk_B)
% 1.33/1.51          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.33/1.51          | ~ (l1_pre_topc @ sk_A))),
% 1.33/1.51      inference('sup-', [status(thm)], ['8', '13'])).
% 1.33/1.51  thf('15', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('17', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.33/1.51             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))
% 1.33/1.51          | (r1_tarski @ 
% 1.33/1.51             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 1.33/1.51             sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.33/1.51  thf('18', plain,
% 1.33/1.51      ((~ (l1_pre_topc @ sk_A)
% 1.33/1.51        | (r1_tarski @ 
% 1.33/1.51           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.33/1.51           sk_B))),
% 1.33/1.51      inference('sup-', [status(thm)], ['5', '17'])).
% 1.33/1.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('20', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(d1_tops_1, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( l1_pre_topc @ A ) =>
% 1.33/1.51       ( ![B:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.33/1.51           ( ( k1_tops_1 @ A @ B ) =
% 1.33/1.51             ( k3_subset_1 @
% 1.33/1.51               ( u1_struct_0 @ A ) @ 
% 1.33/1.51               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.33/1.51  thf('21', plain,
% 1.33/1.51      (![X16 : $i, X17 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.33/1.51          | ((k1_tops_1 @ X17 @ X16)
% 1.33/1.51              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 1.33/1.51                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 1.33/1.51          | ~ (l1_pre_topc @ X17))),
% 1.33/1.51      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.33/1.51  thf('22', plain,
% 1.33/1.51      ((~ (l1_pre_topc @ sk_A)
% 1.33/1.51        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.33/1.51            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51               (k2_pre_topc @ sk_A @ 
% 1.33/1.51                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['20', '21'])).
% 1.33/1.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('24', plain,
% 1.33/1.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.33/1.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.33/1.51      inference('sup-', [status(thm)], ['6', '7'])).
% 1.33/1.51  thf('25', plain,
% 1.33/1.51      (((k1_tops_1 @ sk_A @ sk_B)
% 1.33/1.51         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.33/1.51  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.33/1.51      inference('demod', [status(thm)], ['18', '19', '25'])).
% 1.33/1.51  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 1.33/1.51  
% 1.33/1.51  % SZS output end Refutation
% 1.33/1.51  
% 1.33/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
