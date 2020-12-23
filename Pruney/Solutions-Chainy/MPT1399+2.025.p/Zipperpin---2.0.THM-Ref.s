%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tBtp5H20Ov

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  431 (1178 expanded)
%              Number of equality atoms :    8 (  29 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ X16 @ sk_A )
      | ~ ( v4_pre_topc @ X16 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X16 )
      | ( r2_hidden @ X16 @ sk_C )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ X16 @ sk_A )
      | ~ ( v4_pre_topc @ X16 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X16 )
      | ( r2_hidden @ X16 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('40',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tBtp5H20Ov
% 0.17/0.37  % Computer   : n008.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:43:30 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 70 iterations in 0.032s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(t28_connsp_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @
% 0.23/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.51               ( ~( ( ![D:$i]:
% 0.23/0.51                      ( ( m1_subset_1 @
% 0.23/0.51                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51                        ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.51                          ( ( v3_pre_topc @ D @ A ) & 
% 0.23/0.51                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.23/0.51                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.51            ( l1_pre_topc @ A ) ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.51              ( ![C:$i]:
% 0.23/0.51                ( ( m1_subset_1 @
% 0.23/0.51                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.51                  ( ~( ( ![D:$i]:
% 0.23/0.51                         ( ( m1_subset_1 @
% 0.23/0.51                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51                           ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.51                             ( ( v3_pre_topc @ D @ A ) & 
% 0.23/0.51                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.23/0.51                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.23/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t2_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i]:
% 0.23/0.51         ((r2_hidden @ X4 @ X5)
% 0.23/0.51          | (v1_xboole_0 @ X5)
% 0.23/0.51          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(fc10_tops_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X15 : $i]:
% 0.23/0.51         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.23/0.51          | ~ (l1_pre_topc @ X15)
% 0.23/0.51          | ~ (v2_pre_topc @ X15))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.23/0.51  thf(d3_struct_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X11 : $i]:
% 0.23/0.51         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.23/0.51  thf(fc4_pre_topc, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X14 : $i]:
% 0.23/0.51         ((v4_pre_topc @ (k2_struct_0 @ X14) @ X14)
% 0.23/0.51          | ~ (l1_pre_topc @ X14)
% 0.23/0.51          | ~ (v2_pre_topc @ X14))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X11 : $i]:
% 0.23/0.51         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.23/0.51  thf(d10_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.51  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.51  thf(t3_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X6 : $i, X8 : $i]:
% 0.23/0.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.51  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X16 : $i]:
% 0.23/0.51         (~ (v3_pre_topc @ X16 @ sk_A)
% 0.23/0.51          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.23/0.51          | ~ (r2_hidden @ sk_B @ X16)
% 0.23/0.51          | (r2_hidden @ X16 @ sk_C)
% 0.23/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X16 : $i]:
% 0.23/0.51         (~ (v3_pre_topc @ X16 @ sk_A)
% 0.23/0.51          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.23/0.51          | ~ (r2_hidden @ sk_B @ X16)
% 0.23/0.51          | (r2_hidden @ X16 @ k1_xboole_0)
% 0.23/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['11', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (l1_struct_0 @ sk_A)
% 0.23/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '15'])).
% 0.23/0.51  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(dt_l1_pre_topc, axiom,
% 0.23/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.51  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['16', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '20'])).
% 0.23/0.51  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (l1_struct_0 @ sk_A)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '24'])).
% 0.23/0.51  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['4', '27'])).
% 0.23/0.51  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.51        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '31'])).
% 0.23/0.51  thf(t7_ordinal1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.23/0.51  thf('34', plain,
% 0.23/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.51        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.51  thf('35', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.23/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.51  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.51  thf(fc2_struct_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      (![X13 : $i]:
% 0.23/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.23/0.51          | ~ (l1_struct_0 @ X13)
% 0.23/0.51          | (v2_struct_0 @ X13))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.51  thf('38', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.51  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('40', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.51  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
