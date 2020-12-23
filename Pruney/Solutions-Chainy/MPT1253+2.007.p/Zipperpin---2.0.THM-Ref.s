%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zMql6t7yFL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 7.25s
% Output     : Refutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 136 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 (1404 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ~ ( r1_tarski @ X50 @ X48 )
      | ( r1_tarski @ ( k2_pre_topc @ X49 @ X50 ) @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['20','31','32'])).

thf('34',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','33'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zMql6t7yFL
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.25/7.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.25/7.42  % Solved by: fo/fo7.sh
% 7.25/7.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.25/7.42  % done 12039 iterations in 6.967s
% 7.25/7.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.25/7.42  % SZS output start Refutation
% 7.25/7.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.25/7.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.25/7.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.25/7.42  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.25/7.42  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.25/7.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.25/7.42  thf(sk_B_type, type, sk_B: $i).
% 7.25/7.42  thf(sk_A_type, type, sk_A: $i).
% 7.25/7.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.25/7.42  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.25/7.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.25/7.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.25/7.42  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.25/7.42  thf(t69_tops_1, conjecture,
% 7.25/7.42    (![A:$i]:
% 7.25/7.42     ( ( l1_pre_topc @ A ) =>
% 7.25/7.42       ( ![B:$i]:
% 7.25/7.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.25/7.42           ( ( v4_pre_topc @ B @ A ) =>
% 7.25/7.42             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 7.25/7.42  thf(zf_stmt_0, negated_conjecture,
% 7.25/7.42    (~( ![A:$i]:
% 7.25/7.42        ( ( l1_pre_topc @ A ) =>
% 7.25/7.42          ( ![B:$i]:
% 7.25/7.42            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.25/7.42              ( ( v4_pre_topc @ B @ A ) =>
% 7.25/7.42                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 7.25/7.42    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 7.25/7.42  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('1', plain,
% 7.25/7.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf(dt_k2_tops_1, axiom,
% 7.25/7.42    (![A:$i,B:$i]:
% 7.25/7.42     ( ( ( l1_pre_topc @ A ) & 
% 7.25/7.42         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.25/7.42       ( m1_subset_1 @
% 7.25/7.42         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.25/7.42  thf('2', plain,
% 7.25/7.42      (![X46 : $i, X47 : $i]:
% 7.25/7.42         (~ (l1_pre_topc @ X46)
% 7.25/7.42          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 7.25/7.42          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 7.25/7.42             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 7.25/7.42      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.25/7.42  thf('3', plain,
% 7.25/7.42      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.25/7.42         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.25/7.42        | ~ (l1_pre_topc @ sk_A))),
% 7.25/7.42      inference('sup-', [status(thm)], ['1', '2'])).
% 7.25/7.42  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('5', plain,
% 7.25/7.42      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.25/7.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('demod', [status(thm)], ['3', '4'])).
% 7.25/7.42  thf('6', plain,
% 7.25/7.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf(redefinition_k4_subset_1, axiom,
% 7.25/7.42    (![A:$i,B:$i,C:$i]:
% 7.25/7.42     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.25/7.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.25/7.42       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 7.25/7.42  thf('7', plain,
% 7.25/7.42      (![X36 : $i, X37 : $i, X38 : $i]:
% 7.25/7.42         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 7.25/7.42          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 7.25/7.42          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 7.25/7.42      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 7.25/7.42  thf('8', plain,
% 7.25/7.42      (![X0 : $i]:
% 7.25/7.42         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 7.25/7.42            = (k2_xboole_0 @ sk_B @ X0))
% 7.25/7.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.25/7.42      inference('sup-', [status(thm)], ['6', '7'])).
% 7.25/7.42  thf('9', plain,
% 7.25/7.42      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 7.25/7.42         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('sup-', [status(thm)], ['5', '8'])).
% 7.25/7.42  thf('10', plain,
% 7.25/7.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf(t65_tops_1, axiom,
% 7.25/7.42    (![A:$i]:
% 7.25/7.42     ( ( l1_pre_topc @ A ) =>
% 7.25/7.42       ( ![B:$i]:
% 7.25/7.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.25/7.42           ( ( k2_pre_topc @ A @ B ) =
% 7.25/7.42             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.25/7.42  thf('11', plain,
% 7.25/7.42      (![X53 : $i, X54 : $i]:
% 7.25/7.42         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 7.25/7.42          | ((k2_pre_topc @ X54 @ X53)
% 7.25/7.42              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 7.25/7.42                 (k2_tops_1 @ X54 @ X53)))
% 7.25/7.42          | ~ (l1_pre_topc @ X54))),
% 7.25/7.42      inference('cnf', [status(esa)], [t65_tops_1])).
% 7.25/7.42  thf('12', plain,
% 7.25/7.42      ((~ (l1_pre_topc @ sk_A)
% 7.25/7.42        | ((k2_pre_topc @ sk_A @ sk_B)
% 7.25/7.42            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.25/7.42               (k2_tops_1 @ sk_A @ sk_B))))),
% 7.25/7.42      inference('sup-', [status(thm)], ['10', '11'])).
% 7.25/7.42  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('14', plain,
% 7.25/7.42      (((k2_pre_topc @ sk_A @ sk_B)
% 7.25/7.42         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.25/7.42            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('demod', [status(thm)], ['12', '13'])).
% 7.25/7.42  thf('15', plain,
% 7.25/7.42      (((k2_pre_topc @ sk_A @ sk_B)
% 7.25/7.42         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('sup+', [status(thm)], ['9', '14'])).
% 7.25/7.42  thf('16', plain,
% 7.25/7.42      (((k2_pre_topc @ sk_A @ sk_B)
% 7.25/7.42         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('sup+', [status(thm)], ['9', '14'])).
% 7.25/7.42  thf(t7_xboole_1, axiom,
% 7.25/7.42    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.25/7.42  thf('17', plain,
% 7.25/7.42      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 7.25/7.42      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.25/7.42  thf(d10_xboole_0, axiom,
% 7.25/7.42    (![A:$i,B:$i]:
% 7.25/7.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.25/7.42  thf('18', plain,
% 7.25/7.42      (![X4 : $i, X6 : $i]:
% 7.25/7.42         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 7.25/7.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.25/7.42  thf('19', plain,
% 7.25/7.42      (![X0 : $i, X1 : $i]:
% 7.25/7.42         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 7.25/7.42          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 7.25/7.42      inference('sup-', [status(thm)], ['17', '18'])).
% 7.25/7.42  thf('20', plain,
% 7.25/7.42      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 7.25/7.42        | ((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))),
% 7.25/7.42      inference('sup-', [status(thm)], ['16', '19'])).
% 7.25/7.42  thf('21', plain,
% 7.25/7.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('22', plain,
% 7.25/7.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf(t31_tops_1, axiom,
% 7.25/7.42    (![A:$i]:
% 7.25/7.42     ( ( l1_pre_topc @ A ) =>
% 7.25/7.42       ( ![B:$i]:
% 7.25/7.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.25/7.42           ( ![C:$i]:
% 7.25/7.42             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.25/7.42               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 7.25/7.42                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 7.25/7.42  thf('23', plain,
% 7.25/7.42      (![X48 : $i, X49 : $i, X50 : $i]:
% 7.25/7.42         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 7.25/7.42          | ~ (v4_pre_topc @ X48 @ X49)
% 7.25/7.42          | ~ (r1_tarski @ X50 @ X48)
% 7.25/7.42          | (r1_tarski @ (k2_pre_topc @ X49 @ X50) @ X48)
% 7.25/7.42          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 7.25/7.42          | ~ (l1_pre_topc @ X49))),
% 7.25/7.42      inference('cnf', [status(esa)], [t31_tops_1])).
% 7.25/7.42  thf('24', plain,
% 7.25/7.42      (![X0 : $i]:
% 7.25/7.42         (~ (l1_pre_topc @ sk_A)
% 7.25/7.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.25/7.42          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 7.25/7.42          | ~ (r1_tarski @ X0 @ sk_B)
% 7.25/7.42          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 7.25/7.42      inference('sup-', [status(thm)], ['22', '23'])).
% 7.25/7.42  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('26', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 7.25/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.25/7.42  thf('27', plain,
% 7.25/7.42      (![X0 : $i]:
% 7.25/7.42         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.25/7.42          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 7.25/7.42          | ~ (r1_tarski @ X0 @ sk_B))),
% 7.25/7.42      inference('demod', [status(thm)], ['24', '25', '26'])).
% 7.25/7.42  thf('28', plain,
% 7.25/7.42      ((~ (r1_tarski @ sk_B @ sk_B)
% 7.25/7.42        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 7.25/7.42      inference('sup-', [status(thm)], ['21', '27'])).
% 7.25/7.42  thf('29', plain,
% 7.25/7.42      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 7.25/7.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.25/7.42  thf('30', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 7.25/7.42      inference('simplify', [status(thm)], ['29'])).
% 7.25/7.42  thf('31', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 7.25/7.42      inference('demod', [status(thm)], ['28', '30'])).
% 7.25/7.42  thf('32', plain,
% 7.25/7.42      (((k2_pre_topc @ sk_A @ sk_B)
% 7.25/7.42         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('sup+', [status(thm)], ['9', '14'])).
% 7.25/7.42  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 7.25/7.42      inference('demod', [status(thm)], ['20', '31', '32'])).
% 7.25/7.42  thf('34', plain,
% 7.25/7.42      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.25/7.42      inference('demod', [status(thm)], ['15', '33'])).
% 7.25/7.42  thf(t36_xboole_1, axiom,
% 7.25/7.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.25/7.42  thf('35', plain,
% 7.25/7.42      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 7.25/7.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.25/7.42  thf(t44_xboole_1, axiom,
% 7.25/7.42    (![A:$i,B:$i,C:$i]:
% 7.25/7.42     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 7.25/7.42       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.25/7.42  thf('36', plain,
% 7.25/7.42      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.25/7.42         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 7.25/7.42          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 7.25/7.42      inference('cnf', [status(esa)], [t44_xboole_1])).
% 7.25/7.42  thf('37', plain,
% 7.25/7.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 7.25/7.42      inference('sup-', [status(thm)], ['35', '36'])).
% 7.25/7.42  thf('38', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.25/7.42      inference('sup+', [status(thm)], ['34', '37'])).
% 7.25/7.42  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 7.25/7.42  
% 7.25/7.42  % SZS output end Refutation
% 7.25/7.42  
% 7.25/7.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
