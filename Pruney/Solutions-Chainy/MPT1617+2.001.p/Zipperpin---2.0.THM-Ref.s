%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xjn7qV6WQW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:24 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 107 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  338 (1158 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t25_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_yellow_1])).

thf('0',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( r1_tarski @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v1_tops_2 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','18'])).

thf('20',plain,(
    ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['3','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_tops_2 @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('28',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','18','27'])).

thf('29',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['20','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xjn7qV6WQW
% 0.18/0.37  % Computer   : n015.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 19:41:23 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 31 iterations in 0.015s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.50  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.24/0.50  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.24/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.24/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.24/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(t25_yellow_1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_subset_1 @
% 0.24/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.50           ( ( v1_tops_2 @ B @ A ) <=>
% 0.24/0.50             ( m1_subset_1 @
% 0.24/0.50               B @ 
% 0.24/0.50               ( k1_zfmisc_1 @
% 0.24/0.50                 ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( m1_subset_1 @
% 0.24/0.50                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.50              ( ( v1_tops_2 @ B @ A ) <=>
% 0.24/0.50                ( m1_subset_1 @
% 0.24/0.50                  B @ 
% 0.24/0.50                  ( k1_zfmisc_1 @
% 0.24/0.50                    ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t25_yellow_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      ((~ (m1_subset_1 @ sk_B @ 
% 0.24/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))
% 0.24/0.50        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      ((~ (m1_subset_1 @ sk_B @ 
% 0.24/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))))
% 0.24/0.50         <= (~
% 0.24/0.50             ((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf(t1_yellow_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.24/0.50       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.24/0.50  thf('2', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.24/0.50         <= (~
% 0.24/0.50             ((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (~
% 0.24/0.50       ((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))) | 
% 0.24/0.50       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))
% 0.24/0.50        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))))
% 0.24/0.50         <= (((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('split', [status(esa)], ['5'])).
% 0.24/0.50  thf('7', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.24/0.50         <= (((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.50  thf(t3_subset, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.24/0.50         <= (((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_B @ 
% 0.24/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t78_tops_2, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( l1_pre_topc @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_subset_1 @
% 0.24/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.50           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ X3 @ 
% 0.24/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))
% 0.24/0.50          | ~ (r1_tarski @ X3 @ (u1_pre_topc @ X4))
% 0.24/0.50          | (v1_tops_2 @ X3 @ X4)
% 0.24/0.50          | ~ (l1_pre_topc @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.50        | (v1_tops_2 @ sk_B @ sk_A)
% 0.24/0.50        | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (((v1_tops_2 @ sk_B @ sk_A) | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.24/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      (((v1_tops_2 @ sk_B @ sk_A))
% 0.24/0.50         <= (((m1_subset_1 @ sk_B @ 
% 0.24/0.50               (k1_zfmisc_1 @ 
% 0.24/0.50                (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['10', '15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.24/0.50       ~
% 0.24/0.50       ((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      (~
% 0.24/0.50       ((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))))),
% 0.24/0.50      inference('sat_resolution*', [status(thm)], ['4', '18'])).
% 0.24/0.50  thf('20', plain,
% 0.24/0.50      (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))),
% 0.24/0.50      inference('simpl_trail', [status(thm)], ['3', '19'])).
% 0.24/0.50  thf('21', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_B @ 
% 0.24/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ X3 @ 
% 0.24/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))
% 0.24/0.50          | ~ (v1_tops_2 @ X3 @ X4)
% 0.24/0.50          | (r1_tarski @ X3 @ (u1_pre_topc @ X4))
% 0.24/0.50          | ~ (l1_pre_topc @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.24/0.50  thf('23', plain,
% 0.24/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.50        | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.24/0.50        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.50  thf('26', plain,
% 0.24/0.50      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.24/0.50      inference('split', [status(esa)], ['5'])).
% 0.24/0.50  thf('27', plain,
% 0.24/0.50      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.24/0.50       ((m1_subset_1 @ sk_B @ 
% 0.24/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))))))),
% 0.24/0.50      inference('split', [status(esa)], ['5'])).
% 0.24/0.50  thf('28', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.24/0.50      inference('sat_resolution*', [status(thm)], ['4', '18', '27'])).
% 0.24/0.50  thf('29', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.24/0.50      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.24/0.50  thf('30', plain, ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['25', '29'])).
% 0.24/0.50  thf('31', plain,
% 0.24/0.50      (![X0 : $i, X2 : $i]:
% 0.24/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.50  thf('32', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.50  thf('33', plain, ($false), inference('demod', [status(thm)], ['20', '32'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
