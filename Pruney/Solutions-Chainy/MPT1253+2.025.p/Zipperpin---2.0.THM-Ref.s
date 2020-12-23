%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FqPNhPNrMp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  387 ( 597 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ X19 ) @ ( k2_pre_topc @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','10','15'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FqPNhPNrMp
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 31 iterations in 0.022s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.47  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(t69_tops_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.47             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_pre_topc @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.47                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_tops_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.47             ( k9_subset_1 @
% 0.21/0.47               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.47               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X19 : $i, X20 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.47          | ((k2_tops_1 @ X20 @ X19)
% 0.21/0.47              = (k9_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.47                 (k2_pre_topc @ X20 @ X19) @ 
% 0.21/0.47                 (k2_pre_topc @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19))))
% 0.21/0.47          | ~ (l1_pre_topc @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.47            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_pre_topc @ sk_A @ 
% 0.21/0.47                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t52_pre_topc, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.47             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.47               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.47          | ~ (v4_pre_topc @ X17 @ X18)
% 0.21/0.47          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.21/0.47          | ~ (l1_pre_topc @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.47        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X4 @ X5) = (k6_subset_1 @ X4 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.47         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.47         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.47            (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '10', '15'])).
% 0.21/0.47  thf(dt_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.47  thf(dt_k2_pre_topc, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X15)
% 0.21/0.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.47          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ 
% 0.21/0.47           (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X0)
% 0.21/0.47          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 0.21/0.47              (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)))
% 0.21/0.47              = (k3_xboole_0 @ X2 @ 
% 0.21/0.47                 (k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.47          = (k3_xboole_0 @ sk_B @ 
% 0.21/0.47             (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['16', '21'])).
% 0.21/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.47         = (k3_xboole_0 @ sk_B @ 
% 0.21/0.47            (k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf(t17_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.47  thf('26', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
