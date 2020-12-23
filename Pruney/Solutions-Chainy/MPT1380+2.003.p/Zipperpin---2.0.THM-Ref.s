%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2WPHls1Gdh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  477 (1227 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ( m1_connsp_2 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k1_tops_1 @ X7 @ X6 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( v3_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X8 ) @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_tops_1])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['10','11','26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2WPHls1Gdh
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:30:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.42  % Solved by: fo/fo7.sh
% 0.18/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.42  % done 31 iterations in 0.020s
% 0.18/0.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.42  % SZS output start Refutation
% 0.18/0.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.42  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.42  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.18/0.42  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.18/0.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.42  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.18/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.42  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.18/0.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.42  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.42  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.18/0.42  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.18/0.42  thf(t5_connsp_2, conjecture,
% 0.18/0.42    (![A:$i]:
% 0.18/0.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.42       ( ![B:$i]:
% 0.18/0.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.42           ( ![C:$i]:
% 0.18/0.42             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.42               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.18/0.42                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.18/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.42    (~( ![A:$i]:
% 0.18/0.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.42            ( l1_pre_topc @ A ) ) =>
% 0.18/0.42          ( ![B:$i]:
% 0.18/0.42            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.42              ( ![C:$i]:
% 0.18/0.42                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.42                  ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.18/0.42                    ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ) )),
% 0.18/0.42    inference('cnf.neg', [status(esa)], [t5_connsp_2])).
% 0.18/0.42  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('2', plain,
% 0.18/0.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf(d1_connsp_2, axiom,
% 0.18/0.42    (![A:$i]:
% 0.18/0.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.42       ( ![B:$i]:
% 0.18/0.42         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.42           ( ![C:$i]:
% 0.18/0.42             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.42               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.18/0.42                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.18/0.42  thf('3', plain,
% 0.18/0.42      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.42         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.18/0.42          | ~ (r2_hidden @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.18/0.42          | (m1_connsp_2 @ X12 @ X11 @ X10)
% 0.18/0.42          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.18/0.42          | ~ (l1_pre_topc @ X11)
% 0.18/0.42          | ~ (v2_pre_topc @ X11)
% 0.18/0.42          | (v2_struct_0 @ X11))),
% 0.18/0.42      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.18/0.42  thf('4', plain,
% 0.18/0.42      (![X0 : $i]:
% 0.18/0.42         ((v2_struct_0 @ sk_A)
% 0.18/0.42          | ~ (v2_pre_topc @ sk_A)
% 0.18/0.42          | ~ (l1_pre_topc @ sk_A)
% 0.18/0.42          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.18/0.42          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.18/0.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.42  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('7', plain,
% 0.18/0.42      (![X0 : $i]:
% 0.18/0.42         ((v2_struct_0 @ sk_A)
% 0.18/0.42          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.18/0.42          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.18/0.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.18/0.42  thf('8', plain,
% 0.18/0.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf(d1_tops_1, axiom,
% 0.18/0.42    (![A:$i]:
% 0.18/0.42     ( ( l1_pre_topc @ A ) =>
% 0.18/0.42       ( ![B:$i]:
% 0.18/0.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.42           ( ( k1_tops_1 @ A @ B ) =
% 0.18/0.42             ( k3_subset_1 @
% 0.18/0.42               ( u1_struct_0 @ A ) @ 
% 0.18/0.42               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.18/0.42  thf('9', plain,
% 0.18/0.42      (![X6 : $i, X7 : $i]:
% 0.18/0.42         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.18/0.42          | ((k1_tops_1 @ X7 @ X6)
% 0.18/0.42              = (k3_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.18/0.42                 (k2_pre_topc @ X7 @ (k3_subset_1 @ (u1_struct_0 @ X7) @ X6))))
% 0.18/0.42          | ~ (l1_pre_topc @ X7))),
% 0.18/0.42      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.18/0.42  thf('10', plain,
% 0.18/0.42      ((~ (l1_pre_topc @ sk_A)
% 0.18/0.42        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.18/0.42            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.42               (k2_pre_topc @ sk_A @ 
% 0.18/0.42                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.18/0.42      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.42  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('12', plain,
% 0.18/0.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf(dt_k3_subset_1, axiom,
% 0.18/0.42    (![A:$i,B:$i]:
% 0.18/0.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.42       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.18/0.42  thf('13', plain,
% 0.18/0.42      (![X0 : $i, X1 : $i]:
% 0.18/0.42         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.18/0.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.18/0.42      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.18/0.42  thf('14', plain,
% 0.18/0.42      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.18/0.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.42      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.42  thf(t52_pre_topc, axiom,
% 0.18/0.42    (![A:$i]:
% 0.18/0.42     ( ( l1_pre_topc @ A ) =>
% 0.18/0.42       ( ![B:$i]:
% 0.18/0.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.42           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.18/0.42             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.18/0.42               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.18/0.42  thf('15', plain,
% 0.18/0.42      (![X4 : $i, X5 : $i]:
% 0.18/0.42         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.18/0.42          | ~ (v4_pre_topc @ X4 @ X5)
% 0.18/0.42          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.18/0.42          | ~ (l1_pre_topc @ X5))),
% 0.18/0.42      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.18/0.42  thf('16', plain,
% 0.18/0.42      ((~ (l1_pre_topc @ sk_A)
% 0.18/0.42        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.18/0.42            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.18/0.42        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.18/0.42      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.42  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.42  thf('18', plain,
% 0.18/0.42      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.18/0.42          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.18/0.42        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.18/0.43      inference('demod', [status(thm)], ['16', '17'])).
% 0.18/0.43  thf('19', plain,
% 0.18/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf(fc3_tops_1, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.18/0.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.43       ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ))).
% 0.18/0.43  thf('20', plain,
% 0.18/0.43      (![X8 : $i, X9 : $i]:
% 0.18/0.43         (~ (l1_pre_topc @ X8)
% 0.18/0.43          | ~ (v2_pre_topc @ X8)
% 0.18/0.43          | ~ (v3_pre_topc @ X9 @ X8)
% 0.18/0.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.18/0.43          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X8) @ X9) @ X8))),
% 0.18/0.43      inference('cnf', [status(esa)], [fc3_tops_1])).
% 0.18/0.43  thf('21', plain,
% 0.18/0.43      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.18/0.43        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.18/0.43        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.43        | ~ (l1_pre_topc @ sk_A))),
% 0.18/0.43      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.43  thf('22', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('25', plain,
% 0.18/0.43      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.18/0.43      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.18/0.43  thf('26', plain,
% 0.18/0.43      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.18/0.43         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.18/0.43      inference('demod', [status(thm)], ['18', '25'])).
% 0.18/0.43  thf('27', plain,
% 0.18/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf(involutiveness_k3_subset_1, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.43       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.18/0.43  thf('28', plain,
% 0.18/0.43      (![X2 : $i, X3 : $i]:
% 0.18/0.43         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.18/0.43          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.18/0.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.18/0.43  thf('29', plain,
% 0.18/0.43      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.43         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.18/0.43      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.43  thf('30', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.18/0.43      inference('demod', [status(thm)], ['10', '11', '26', '29'])).
% 0.18/0.43  thf('31', plain,
% 0.18/0.43      (![X0 : $i]:
% 0.18/0.43         ((v2_struct_0 @ sk_A)
% 0.18/0.43          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.18/0.43          | ~ (r2_hidden @ X0 @ sk_B)
% 0.18/0.43          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.43      inference('demod', [status(thm)], ['7', '30'])).
% 0.18/0.43  thf('32', plain,
% 0.18/0.43      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.18/0.43        | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)
% 0.18/0.43        | (v2_struct_0 @ sk_A))),
% 0.18/0.43      inference('sup-', [status(thm)], ['1', '31'])).
% 0.18/0.43  thf('33', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('34', plain,
% 0.18/0.43      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.18/0.43      inference('demod', [status(thm)], ['32', '33'])).
% 0.18/0.43  thf('35', plain, (~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C)),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('36', plain, ((v2_struct_0 @ sk_A)),
% 0.18/0.43      inference('clc', [status(thm)], ['34', '35'])).
% 0.18/0.43  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.18/0.43  
% 0.18/0.43  % SZS output end Refutation
% 0.18/0.43  
% 0.18/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
