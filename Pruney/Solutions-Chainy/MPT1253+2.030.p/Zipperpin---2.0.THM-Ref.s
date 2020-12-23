%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0c1HRUqeU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 108 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  494 (1185 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ X10 ) @ ( k3_subset_1 @ X9 @ ( k9_subset_1 @ X9 @ X10 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_tops_1 @ X16 @ X15 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','21'])).

thf('23',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','22'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X6 @ X5 ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','21'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0c1HRUqeU
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.88  % Solved by: fo/fo7.sh
% 1.65/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.88  % done 837 iterations in 1.462s
% 1.65/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.88  % SZS output start Refutation
% 1.65/1.88  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.65/1.88  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.65/1.88  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.65/1.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.65/1.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.65/1.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.65/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.65/1.88  thf(t69_tops_1, conjecture,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( v4_pre_topc @ B @ A ) =>
% 1.65/1.88             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.65/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.88    (~( ![A:$i]:
% 1.65/1.88        ( ( l1_pre_topc @ A ) =>
% 1.65/1.88          ( ![B:$i]:
% 1.65/1.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88              ( ( v4_pre_topc @ B @ A ) =>
% 1.65/1.88                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 1.65/1.88    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 1.65/1.88  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('1', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('2', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(dt_k3_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.65/1.88  thf('3', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.65/1.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.65/1.88  thf('4', plain,
% 1.65/1.88      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['2', '3'])).
% 1.65/1.88  thf(dt_k2_pre_topc, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.88       ( m1_subset_1 @
% 1.65/1.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.88  thf('5', plain,
% 1.65/1.88      (![X11 : $i, X12 : $i]:
% 1.65/1.88         (~ (l1_pre_topc @ X11)
% 1.65/1.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.65/1.88          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 1.65/1.88             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.65/1.88  thf('6', plain,
% 1.65/1.88      (((m1_subset_1 @ 
% 1.65/1.88         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.65/1.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['4', '5'])).
% 1.65/1.88  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('8', plain,
% 1.65/1.88      ((m1_subset_1 @ 
% 1.65/1.88        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.65/1.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('demod', [status(thm)], ['6', '7'])).
% 1.65/1.88  thf(t42_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88       ( ![C:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88           ( r1_tarski @
% 1.65/1.88             ( k3_subset_1 @ A @ B ) @ 
% 1.65/1.88             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.65/1.88  thf('9', plain,
% 1.65/1.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.65/1.88          | (r1_tarski @ (k3_subset_1 @ X9 @ X10) @ 
% 1.65/1.88             (k3_subset_1 @ X9 @ (k9_subset_1 @ X9 @ X10 @ X8)))
% 1.65/1.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t42_subset_1])).
% 1.65/1.88  thf('10', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.65/1.88             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.88               (k2_pre_topc @ sk_A @ 
% 1.65/1.88                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.88  thf('11', plain,
% 1.65/1.88      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.88        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.65/1.88          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['1', '10'])).
% 1.65/1.88  thf('12', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(d2_tops_1, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( k2_tops_1 @ A @ B ) =
% 1.65/1.88             ( k9_subset_1 @
% 1.65/1.88               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.65/1.88               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.65/1.88  thf('13', plain,
% 1.65/1.88      (![X15 : $i, X16 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.65/1.88          | ((k2_tops_1 @ X16 @ X15)
% 1.65/1.88              = (k9_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.65/1.88                 (k2_pre_topc @ X16 @ X15) @ 
% 1.65/1.88                 (k2_pre_topc @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15))))
% 1.65/1.88          | ~ (l1_pre_topc @ X16))),
% 1.65/1.88      inference('cnf', [status(esa)], [d2_tops_1])).
% 1.65/1.88  thf('14', plain,
% 1.65/1.88      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.88        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.88               (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.65/1.88               (k2_pre_topc @ sk_A @ 
% 1.65/1.88                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['12', '13'])).
% 1.65/1.88  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('16', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf(t52_pre_topc, axiom,
% 1.65/1.88    (![A:$i]:
% 1.65/1.88     ( ( l1_pre_topc @ A ) =>
% 1.65/1.88       ( ![B:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.88           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.65/1.88             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.65/1.88               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.65/1.88  thf('17', plain,
% 1.65/1.88      (![X13 : $i, X14 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.65/1.88          | ~ (v4_pre_topc @ X13 @ X14)
% 1.65/1.88          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 1.65/1.88          | ~ (l1_pre_topc @ X14))),
% 1.65/1.88      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.65/1.88  thf('18', plain,
% 1.65/1.88      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.88        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.65/1.88        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.65/1.88      inference('sup-', [status(thm)], ['16', '17'])).
% 1.65/1.88  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('20', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('21', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.65/1.88      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.65/1.88  thf('22', plain,
% 1.65/1.88      (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.65/1.88            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.65/1.88      inference('demod', [status(thm)], ['14', '15', '21'])).
% 1.65/1.88  thf('23', plain,
% 1.65/1.88      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.88        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.88      inference('demod', [status(thm)], ['11', '22'])).
% 1.65/1.88  thf(t31_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88       ( ![C:$i]:
% 1.65/1.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88           ( ( r1_tarski @ B @ C ) <=>
% 1.65/1.88             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.88  thf('24', plain,
% 1.65/1.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.88         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.65/1.88          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ (k3_subset_1 @ X6 @ X7))
% 1.65/1.88          | (r1_tarski @ X7 @ X5)
% 1.65/1.88          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.65/1.88  thf('25', plain,
% 1.65/1.88      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.88        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.65/1.88        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.88      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.88  thf('26', plain,
% 1.65/1.88      (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.88         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.65/1.88            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.65/1.88      inference('demod', [status(thm)], ['14', '15', '21'])).
% 1.65/1.88  thf('27', plain,
% 1.65/1.88      ((m1_subset_1 @ 
% 1.65/1.88        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.65/1.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('demod', [status(thm)], ['6', '7'])).
% 1.65/1.88  thf(dt_k9_subset_1, axiom,
% 1.65/1.88    (![A:$i,B:$i,C:$i]:
% 1.65/1.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.88       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.65/1.88  thf('28', plain,
% 1.65/1.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.88         ((m1_subset_1 @ (k9_subset_1 @ X2 @ X3 @ X4) @ (k1_zfmisc_1 @ X2))
% 1.65/1.88          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X2)))),
% 1.65/1.88      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.65/1.88  thf('29', plain,
% 1.65/1.88      (![X0 : $i]:
% 1.65/1.88         (m1_subset_1 @ 
% 1.65/1.88          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.88           (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.65/1.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.88  thf('30', plain,
% 1.65/1.88      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['26', '29'])).
% 1.65/1.88  thf('31', plain,
% 1.65/1.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.88  thf('32', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.65/1.88      inference('demod', [status(thm)], ['25', '30', '31'])).
% 1.65/1.88  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 1.65/1.88  
% 1.65/1.88  % SZS output end Refutation
% 1.65/1.88  
% 1.65/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
