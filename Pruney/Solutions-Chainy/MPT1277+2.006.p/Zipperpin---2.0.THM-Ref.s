%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6IDXW4Xhi

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 578 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t96_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tops_1])).

thf('0',plain,(
    ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
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

thf(t95_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X7 @ X6 ) @ X7 )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t95_tops_1])).

thf('5',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v4_pre_topc @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_tops_1])).

thf('10',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['5','6','7','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_tops_1 @ X5 @ X4 )
        = ( k2_tops_1 @ X5 @ ( k3_subset_1 @ ( u1_struct_0 @ X5 ) @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6IDXW4Xhi
% 0.12/0.37  % Computer   : n018.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 20:19:42 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.38  % Python version: Python 3.6.8
% 0.12/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 20 iterations in 0.018s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.23/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.48  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.23/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.48  thf(t96_tops_1, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( v4_pre_topc @ B @ A ) =>
% 0.23/0.48             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48          ( ![B:$i]:
% 0.23/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48              ( ( v4_pre_topc @ B @ A ) =>
% 0.23/0.48                ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t96_tops_1])).
% 0.23/0.48  thf('0', plain, (~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(dt_k3_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]:
% 0.23/0.48         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.23/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.23/0.48      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.48  thf(t95_tops_1, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( v3_pre_topc @ B @ A ) =>
% 0.23/0.48             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X6 : $i, X7 : $i]:
% 0.23/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.23/0.48          | (v3_tops_1 @ (k2_tops_1 @ X7 @ X6) @ X7)
% 0.23/0.48          | ~ (v3_pre_topc @ X6 @ X7)
% 0.23/0.48          | ~ (l1_pre_topc @ X7)
% 0.23/0.48          | ~ (v2_pre_topc @ X7))),
% 0.23/0.48      inference('cnf', [status(esa)], [t95_tops_1])).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.48        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.23/0.48        | (v3_tops_1 @ 
% 0.23/0.48           (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.23/0.48           sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.48  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(fc2_tops_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.23/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48       ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ))).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      (![X2 : $i, X3 : $i]:
% 0.23/0.48         (~ (l1_pre_topc @ X2)
% 0.23/0.48          | ~ (v2_pre_topc @ X2)
% 0.23/0.48          | ~ (v4_pre_topc @ X3 @ X2)
% 0.23/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.23/0.48          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X2) @ X3) @ X2))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc2_tops_1])).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.23/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.23/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.48  thf('11', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('14', plain,
% 0.23/0.48      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.23/0.48      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      ((v3_tops_1 @ 
% 0.23/0.48        (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ sk_A)),
% 0.23/0.48      inference('demod', [status(thm)], ['5', '6', '7', '14'])).
% 0.23/0.48  thf('16', plain,
% 0.23/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t62_tops_1, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( l1_pre_topc @ A ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( k2_tops_1 @ A @ B ) =
% 0.23/0.48             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.23/0.48  thf('17', plain,
% 0.23/0.48      (![X4 : $i, X5 : $i]:
% 0.23/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.23/0.48          | ((k2_tops_1 @ X5 @ X4)
% 0.23/0.48              = (k2_tops_1 @ X5 @ (k3_subset_1 @ (u1_struct_0 @ X5) @ X4)))
% 0.23/0.48          | ~ (l1_pre_topc @ X5))),
% 0.23/0.48      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.48        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.48            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('20', plain,
% 0.23/0.48      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.48         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.23/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.48  thf('21', plain, ((v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.48      inference('demod', [status(thm)], ['15', '20'])).
% 0.23/0.48  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
