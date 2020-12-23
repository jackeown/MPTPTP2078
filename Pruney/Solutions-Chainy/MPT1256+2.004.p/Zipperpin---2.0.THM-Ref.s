%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MB0ayTH8EF

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:17 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   51 (  83 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  436 ( 882 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t72_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) @ ( k2_tops_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_tops_1 @ X9 @ X8 )
        = ( k2_tops_1 @ X9 @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ X6 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('23',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_tops_1 @ X9 @ X8 )
        = ( k2_tops_1 @ X9 @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('29',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','23','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MB0ayTH8EF
% 0.16/0.39  % Computer   : n025.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 19:49:36 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.40/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.56  % Solved by: fo/fo7.sh
% 0.40/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.56  % done 69 iterations in 0.055s
% 0.40/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.56  % SZS output start Refutation
% 0.40/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.56  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.56  thf(t72_tops_1, conjecture,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( l1_pre_topc @ A ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56           ( r1_tarski @
% 0.40/0.56             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.40/0.56             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.40/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.56    (~( ![A:$i]:
% 0.40/0.56        ( ( l1_pre_topc @ A ) =>
% 0.40/0.56          ( ![B:$i]:
% 0.40/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56              ( r1_tarski @
% 0.40/0.56                ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.40/0.56                ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 0.40/0.56    inference('cnf.neg', [status(esa)], [t72_tops_1])).
% 0.40/0.56  thf('0', plain,
% 0.40/0.56      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.40/0.56          (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('1', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(dt_k3_subset_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.56  thf('2', plain,
% 0.40/0.56      (![X0 : $i, X1 : $i]:
% 0.40/0.56         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.40/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.40/0.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.56  thf('3', plain,
% 0.40/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.56  thf(t71_tops_1, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( l1_pre_topc @ A ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56           ( r1_tarski @
% 0.40/0.56             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.40/0.56  thf('4', plain,
% 0.40/0.56      (![X10 : $i, X11 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.40/0.56          | (r1_tarski @ (k2_tops_1 @ X11 @ (k1_tops_1 @ X11 @ X10)) @ 
% 0.40/0.56             (k2_tops_1 @ X11 @ X10))
% 0.40/0.56          | ~ (l1_pre_topc @ X11))),
% 0.40/0.56      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.40/0.56  thf('5', plain,
% 0.40/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.56        | (r1_tarski @ 
% 0.40/0.56           (k2_tops_1 @ sk_A @ 
% 0.40/0.56            (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.40/0.56           (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.56  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('7', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(dt_k2_pre_topc, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.56       ( m1_subset_1 @
% 0.40/0.56         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.56  thf('8', plain,
% 0.40/0.56      (![X4 : $i, X5 : $i]:
% 0.40/0.56         (~ (l1_pre_topc @ X4)
% 0.40/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.40/0.56          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 0.40/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.40/0.56      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.40/0.56  thf('9', plain,
% 0.40/0.56      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('11', plain,
% 0.40/0.56      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.56  thf(t62_tops_1, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( l1_pre_topc @ A ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56           ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.56             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.56  thf('12', plain,
% 0.40/0.56      (![X8 : $i, X9 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.40/0.56          | ((k2_tops_1 @ X9 @ X8)
% 0.40/0.56              = (k2_tops_1 @ X9 @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8)))
% 0.40/0.56          | ~ (l1_pre_topc @ X9))),
% 0.40/0.56      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.40/0.56  thf('13', plain,
% 0.40/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.56        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.40/0.56            = (k2_tops_1 @ sk_A @ 
% 0.40/0.56               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56                (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.40/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('15', plain,
% 0.40/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.56  thf(d1_tops_1, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( l1_pre_topc @ A ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.56           ( ( k1_tops_1 @ A @ B ) =
% 0.40/0.56             ( k3_subset_1 @
% 0.40/0.56               ( u1_struct_0 @ A ) @ 
% 0.40/0.56               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.40/0.56  thf('16', plain,
% 0.40/0.56      (![X6 : $i, X7 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.40/0.56          | ((k1_tops_1 @ X7 @ X6)
% 0.40/0.56              = (k3_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.40/0.56                 (k2_pre_topc @ X7 @ (k3_subset_1 @ (u1_struct_0 @ X7) @ X6))))
% 0.40/0.56          | ~ (l1_pre_topc @ X7))),
% 0.40/0.56      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.40/0.56  thf('17', plain,
% 0.40/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.56        | ((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.56            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56               (k2_pre_topc @ sk_A @ 
% 0.40/0.56                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 0.40/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.56  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('19', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(involutiveness_k3_subset_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.40/0.56  thf('20', plain,
% 0.40/0.56      (![X2 : $i, X3 : $i]:
% 0.40/0.56         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.40/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.40/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.40/0.56  thf('21', plain,
% 0.40/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.40/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.56  thf('22', plain,
% 0.40/0.56      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.56         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.40/0.56      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.40/0.56  thf('23', plain,
% 0.40/0.56      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.40/0.56         = (k2_tops_1 @ sk_A @ 
% 0.40/0.56            (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.56      inference('demod', [status(thm)], ['13', '14', '22'])).
% 0.40/0.56  thf('24', plain,
% 0.40/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.56  thf('25', plain,
% 0.40/0.56      (![X8 : $i, X9 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.40/0.56          | ((k2_tops_1 @ X9 @ X8)
% 0.40/0.56              = (k2_tops_1 @ X9 @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8)))
% 0.40/0.56          | ~ (l1_pre_topc @ X9))),
% 0.40/0.56      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.40/0.56  thf('26', plain,
% 0.40/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.56        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.56            = (k2_tops_1 @ sk_A @ 
% 0.40/0.56               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('28', plain,
% 0.40/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.56         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.40/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.56  thf('29', plain,
% 0.40/0.56      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.56         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.56  thf('30', plain,
% 0.40/0.56      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.40/0.56        (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.56      inference('demod', [status(thm)], ['5', '6', '23', '29'])).
% 0.40/0.56  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.40/0.56  
% 0.40/0.56  % SZS output end Refutation
% 0.40/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
