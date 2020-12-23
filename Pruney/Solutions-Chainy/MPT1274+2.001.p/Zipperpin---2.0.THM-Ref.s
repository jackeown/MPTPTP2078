%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lbozqxUTfC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  289 ( 586 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(t93_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v2_tops_1 @ B @ A )
                & ( v4_pre_topc @ B @ A ) )
             => ( v3_tops_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X6 @ X5 ) @ X6 )
      | ( v3_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( r1_tarski @ X3 @ ( k2_pre_topc @ X4 @ X3 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X9 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['6','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lbozqxUTfC
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 18 iterations in 0.013s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.47  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.20/0.47  thf(t93_tops_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.47             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( l1_pre_topc @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.47                ( v3_tops_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t93_tops_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d5_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v3_tops_1 @ B @ A ) <=>
% 0.20/0.47             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.47          | ~ (v2_tops_1 @ (k2_pre_topc @ X6 @ X5) @ X6)
% 0.20/0.47          | (v3_tops_1 @ X5 @ X6)
% 0.20/0.47          | ~ (l1_pre_topc @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, (~ (v3_tops_1 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, (~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t48_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | (r1_tarski @ X3 @ (k2_pre_topc @ X4 @ X3))
% 0.20/0.47          | ~ (l1_pre_topc @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.47        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t31_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.47                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.47          | ~ (v4_pre_topc @ X7 @ X8)
% 0.20/0.47          | ~ (r1_tarski @ X9 @ X7)
% 0.20/0.47          | (r1_tarski @ (k2_pre_topc @ X8 @ X9) @ X7)
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.47          | ~ (l1_pre_topc @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.20/0.47          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.47          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.20/0.47          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.47        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '23'])).
% 0.20/0.47  thf('25', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '24'])).
% 0.20/0.47  thf('26', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '25', '26'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
