%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.meu3pcQ0yN

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  406 ( 890 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('2',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
   <= ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('5',plain,
    ( ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
    | ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference(simpl_trail,[status(thm)],['2','11'])).

thf('13',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc13_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_tops_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_tops_1 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_tops_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v2_tops_1 @ X8 @ X9 )
      | ~ ( v3_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( k1_xboole_0
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['13','29','30','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.meu3pcQ0yN
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:50:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 30 iterations in 0.025s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.19/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.47  thf(t97_tops_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.19/0.47             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.19/0.47                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t55_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( l1_pre_topc @ B ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47               ( ![D:$i]:
% 0.19/0.47                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.47                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.47                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.19/0.47                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.19/0.47                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47          | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47          | ((k1_tops_1 @ X4 @ X5) = (X5))
% 0.19/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47          | ~ (l1_pre_topc @ X7)
% 0.19/0.47          | ~ (v2_pre_topc @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((![X4 : $i, X5 : $i]:
% 0.19/0.47          (~ (l1_pre_topc @ X4)
% 0.19/0.47           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47           | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47           | ((k1_tops_1 @ X4 @ X5) = (X5))))
% 0.19/0.47         <= ((![X4 : $i, X5 : $i]:
% 0.19/0.47                (~ (l1_pre_topc @ X4)
% 0.19/0.47                 | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47                 | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47                 | ((k1_tops_1 @ X4 @ X5) = (X5)))))),
% 0.19/0.47      inference('split', [status(esa)], ['1'])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47          | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47          | ((k1_tops_1 @ X4 @ X5) = (X5))
% 0.19/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47          | ~ (l1_pre_topc @ X7)
% 0.19/0.47          | ~ (v2_pre_topc @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      ((![X6 : $i, X7 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47           | ~ (l1_pre_topc @ X7)
% 0.19/0.47           | ~ (v2_pre_topc @ X7)))
% 0.19/0.47         <= ((![X6 : $i, X7 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47                 | ~ (l1_pre_topc @ X7)
% 0.19/0.47                 | ~ (v2_pre_topc @ X7))))),
% 0.19/0.47      inference('split', [status(esa)], ['4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.19/0.47         <= ((![X6 : $i, X7 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47                 | ~ (l1_pre_topc @ X7)
% 0.19/0.47                 | ~ (v2_pre_topc @ X7))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '5'])).
% 0.19/0.47  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (~
% 0.19/0.47       (![X6 : $i, X7 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47           | ~ (l1_pre_topc @ X7)
% 0.19/0.47           | ~ (v2_pre_topc @ X7)))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((![X4 : $i, X5 : $i]:
% 0.19/0.47          (~ (l1_pre_topc @ X4)
% 0.19/0.47           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47           | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47           | ((k1_tops_1 @ X4 @ X5) = (X5)))) | 
% 0.19/0.47       (![X6 : $i, X7 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.47           | ~ (l1_pre_topc @ X7)
% 0.19/0.47           | ~ (v2_pre_topc @ X7)))),
% 0.19/0.47      inference('split', [status(esa)], ['4'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((![X4 : $i, X5 : $i]:
% 0.19/0.47          (~ (l1_pre_topc @ X4)
% 0.19/0.47           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47           | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47           | ((k1_tops_1 @ X4 @ X5) = (X5))))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.47          | ~ (v3_pre_topc @ X5 @ X4)
% 0.19/0.47          | ((k1_tops_1 @ X4 @ X5) = (X5)))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['2', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.19/0.47        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(fc13_tops_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( l1_pre_topc @ A ) & ( v2_tops_1 @ B @ A ) & 
% 0.19/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.47       ( v1_xboole_0 @ ( k1_tops_1 @ A @ B ) ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (l1_pre_topc @ X2)
% 0.19/0.47          | ~ (v2_tops_1 @ X3 @ X2)
% 0.19/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.19/0.47          | (v1_xboole_0 @ (k1_tops_1 @ X2 @ X3)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc13_tops_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.19/0.47        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t92_tops_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_pre_topc @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.47           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.47          | (v2_tops_1 @ X8 @ X9)
% 0.19/0.47          | ~ (v3_tops_1 @ X8 @ X9)
% 0.19/0.47          | ~ (l1_pre_topc @ X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.47        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.19/0.47        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('23', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.19/0.47  thf('25', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '24'])).
% 0.19/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.47  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.47  thf(t8_boole, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf('29', plain, (((k1_xboole_0) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.47  thf('30', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('32', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '29', '30', '31'])).
% 0.19/0.47  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('34', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
