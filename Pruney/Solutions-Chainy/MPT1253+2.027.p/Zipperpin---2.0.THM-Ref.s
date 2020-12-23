%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vDoXweKtDq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  380 ( 590 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','10','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vDoXweKtDq
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:27:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 285 iterations in 0.238s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(t69_tops_1, conjecture,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70           ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.70             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i]:
% 0.45/0.70        ( ( l1_pre_topc @ A ) =>
% 0.45/0.70          ( ![B:$i]:
% 0.45/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70              ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.70                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.45/0.70  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(d2_tops_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70           ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.70             ( k9_subset_1 @
% 0.45/0.70               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.45/0.70               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (![X18 : $i, X19 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.70          | ((k2_tops_1 @ X19 @ X18)
% 0.45/0.70              = (k9_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.45/0.70                 (k2_pre_topc @ X19 @ X18) @ 
% 0.45/0.70                 (k2_pre_topc @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18))))
% 0.45/0.70          | ~ (l1_pre_topc @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.70        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.70            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.70               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.70               (k2_pre_topc @ sk_A @ 
% 0.45/0.70                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.70  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(t52_pre_topc, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_pre_topc @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.70             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.70               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (![X16 : $i, X17 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.70          | ~ (v4_pre_topc @ X16 @ X17)
% 0.45/0.70          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.45/0.70          | ~ (l1_pre_topc @ X17))),
% 0.45/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.70        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.45/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.70  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.45/0.70      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(d5_subset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.45/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.45/0.70         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.70         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.70            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.70      inference('demod', [status(thm)], ['3', '4', '10', '13'])).
% 0.45/0.70  thf(t36_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.45/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.70  thf(t3_subset, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (![X11 : $i, X13 : $i]:
% 0.45/0.70         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.70  thf(dt_k2_pre_topc, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.70       ( m1_subset_1 @
% 0.45/0.70         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X14 : $i, X15 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X14)
% 0.45/0.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.70          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.45/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((m1_subset_1 @ 
% 0.45/0.70           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.70          | ~ (l1_pre_topc @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.70  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.70       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.70         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.45/0.70          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (l1_pre_topc @ X0)
% 0.45/0.70          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.45/0.70              (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))
% 0.45/0.70              = (k3_xboole_0 @ X2 @ 
% 0.45/0.70                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.70          = (k3_xboole_0 @ sk_B @ 
% 0.45/0.70             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.70      inference('sup+', [status(thm)], ['14', '21'])).
% 0.45/0.70  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.70         = (k3_xboole_0 @ sk_B @ 
% 0.45/0.70            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.70  thf(t17_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.45/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.70  thf('26', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.45/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.70  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
