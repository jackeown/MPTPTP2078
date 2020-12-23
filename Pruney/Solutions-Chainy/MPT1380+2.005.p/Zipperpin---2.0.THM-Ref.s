%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfV4g1YwyL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  428 (1116 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t5_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( r2_hidden @ C @ B ) )
                 => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_tops_1 @ X5 @ X6 ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('9',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) )
   <= ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B )
        = sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('16',plain,
    ( ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) )
   <= ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v3_pre_topc @ X1 @ X0 )
        | ( ( k1_tops_1 @ X0 @ X1 )
          = X1 ) )
    | ! [X2: $i,X3: $i] :
        ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
        | ~ ( l1_pre_topc @ X3 )
        | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = X1 ) ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NfV4g1YwyL
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:47:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 20 iterations in 0.014s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.49  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.49  thf(t5_connsp_2, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49           ( ![C:$i]:
% 0.23/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.23/0.49                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.49            ( l1_pre_topc @ A ) ) =>
% 0.23/0.49          ( ![B:$i]:
% 0.23/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49              ( ![C:$i]:
% 0.23/0.49                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49                  ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.23/0.49                    ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t5_connsp_2])).
% 0.23/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(d1_connsp_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49           ( ![C:$i]:
% 0.23/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.23/0.49                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.23/0.49          | ~ (r2_hidden @ X4 @ (k1_tops_1 @ X5 @ X6))
% 0.23/0.49          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.23/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.23/0.49          | ~ (l1_pre_topc @ X5)
% 0.23/0.49          | ~ (v2_pre_topc @ X5)
% 0.23/0.49          | (v2_struct_0 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.49          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.23/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t55_tops_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( l1_pre_topc @ B ) =>
% 0.23/0.49           ( ![C:$i]:
% 0.23/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49               ( ![D:$i]:
% 0.23/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.49                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.23/0.49                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.23/0.49                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.23/0.49                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (l1_pre_topc @ X0)
% 0.23/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49          | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49          | ((k1_tops_1 @ X0 @ X1) = (X1))
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49          | ~ (l1_pre_topc @ X3)
% 0.23/0.49          | ~ (v2_pre_topc @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      ((![X0 : $i, X1 : $i]:
% 0.23/0.49          (~ (l1_pre_topc @ X0)
% 0.23/0.49           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49           | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49           | ((k1_tops_1 @ X0 @ X1) = (X1))))
% 0.23/0.49         <= ((![X0 : $i, X1 : $i]:
% 0.23/0.49                (~ (l1_pre_topc @ X0)
% 0.23/0.49                 | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49                 | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49                 | ((k1_tops_1 @ X0 @ X1) = (X1)))))),
% 0.23/0.49      inference('split', [status(esa)], ['8'])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.23/0.49         | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.23/0.49         | ~ (l1_pre_topc @ sk_A)))
% 0.23/0.49         <= ((![X0 : $i, X1 : $i]:
% 0.23/0.49                (~ (l1_pre_topc @ X0)
% 0.23/0.49                 | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49                 | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49                 | ((k1_tops_1 @ X0 @ X1) = (X1)))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['7', '9'])).
% 0.23/0.49  thf('11', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.23/0.49         <= ((![X0 : $i, X1 : $i]:
% 0.23/0.49                (~ (l1_pre_topc @ X0)
% 0.23/0.49                 | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49                 | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49                 | ((k1_tops_1 @ X0 @ X1) = (X1)))))),
% 0.23/0.49      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (l1_pre_topc @ X0)
% 0.23/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49          | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49          | ((k1_tops_1 @ X0 @ X1) = (X1))
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49          | ~ (l1_pre_topc @ X3)
% 0.23/0.49          | ~ (v2_pre_topc @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      ((![X2 : $i, X3 : $i]:
% 0.23/0.49          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49           | ~ (l1_pre_topc @ X3)
% 0.23/0.49           | ~ (v2_pre_topc @ X3)))
% 0.23/0.49         <= ((![X2 : $i, X3 : $i]:
% 0.23/0.49                (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49                 | ~ (l1_pre_topc @ X3)
% 0.23/0.49                 | ~ (v2_pre_topc @ X3))))),
% 0.23/0.49      inference('split', [status(esa)], ['15'])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.23/0.49         <= ((![X2 : $i, X3 : $i]:
% 0.23/0.49                (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49                 | ~ (l1_pre_topc @ X3)
% 0.23/0.49                 | ~ (v2_pre_topc @ X3))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '16'])).
% 0.23/0.49  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      (~
% 0.23/0.49       (![X2 : $i, X3 : $i]:
% 0.23/0.49          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49           | ~ (l1_pre_topc @ X3)
% 0.23/0.49           | ~ (v2_pre_topc @ X3)))),
% 0.23/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.23/0.49  thf('21', plain,
% 0.23/0.49      ((![X0 : $i, X1 : $i]:
% 0.23/0.49          (~ (l1_pre_topc @ X0)
% 0.23/0.49           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49           | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49           | ((k1_tops_1 @ X0 @ X1) = (X1)))) | 
% 0.23/0.49       (![X2 : $i, X3 : $i]:
% 0.23/0.49          (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.49           | ~ (l1_pre_topc @ X3)
% 0.23/0.49           | ~ (v2_pre_topc @ X3)))),
% 0.23/0.49      inference('split', [status(esa)], ['15'])).
% 0.23/0.49  thf('22', plain,
% 0.23/0.49      ((![X0 : $i, X1 : $i]:
% 0.23/0.49          (~ (l1_pre_topc @ X0)
% 0.23/0.49           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.49           | ~ (v3_pre_topc @ X1 @ X0)
% 0.23/0.49           | ((k1_tops_1 @ X0 @ X1) = (X1))))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.23/0.49  thf('23', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['13', '22'])).
% 0.23/0.49  thf('24', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.23/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('demod', [status(thm)], ['4', '5', '6', '23'])).
% 0.23/0.49  thf('25', plain,
% 0.23/0.49      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.23/0.49        | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '24'])).
% 0.23/0.49  thf('26', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('27', plain,
% 0.23/0.49      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.23/0.49  thf('28', plain, (~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('29', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.49  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
