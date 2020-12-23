%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTB8iVpc9X

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:16 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  478 ( 808 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ X7 ) @ ( k3_subset_1 @ X6 @ ( k9_subset_1 @ X6 @ X7 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_tops_1 @ X13 @ X12 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ X12 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ( r1_tarski @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTB8iVpc9X
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.25/3.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.25/3.52  % Solved by: fo/fo7.sh
% 3.25/3.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.25/3.52  % done 1362 iterations in 3.066s
% 3.25/3.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.25/3.52  % SZS output start Refutation
% 3.25/3.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.25/3.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.25/3.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.25/3.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.25/3.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.25/3.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.25/3.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.25/3.52  thf(sk_A_type, type, sk_A: $i).
% 3.25/3.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.25/3.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.25/3.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.25/3.52  thf(sk_B_type, type, sk_B: $i).
% 3.25/3.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.25/3.52  thf(t69_tops_1, conjecture,
% 3.25/3.52    (![A:$i]:
% 3.25/3.52     ( ( l1_pre_topc @ A ) =>
% 3.25/3.52       ( ![B:$i]:
% 3.25/3.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.25/3.52           ( ( v4_pre_topc @ B @ A ) =>
% 3.25/3.52             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 3.25/3.52  thf(zf_stmt_0, negated_conjecture,
% 3.25/3.52    (~( ![A:$i]:
% 3.25/3.52        ( ( l1_pre_topc @ A ) =>
% 3.25/3.52          ( ![B:$i]:
% 3.25/3.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.25/3.52              ( ( v4_pre_topc @ B @ A ) =>
% 3.25/3.52                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 3.25/3.52    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 3.25/3.52  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('1', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('2', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf(dt_k3_subset_1, axiom,
% 3.25/3.52    (![A:$i,B:$i]:
% 3.25/3.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.25/3.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.25/3.52  thf('3', plain,
% 3.25/3.52      (![X0 : $i, X1 : $i]:
% 3.25/3.52         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 3.25/3.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.25/3.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.25/3.52  thf('4', plain,
% 3.25/3.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.25/3.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('sup-', [status(thm)], ['2', '3'])).
% 3.25/3.52  thf(dt_k2_pre_topc, axiom,
% 3.25/3.52    (![A:$i,B:$i]:
% 3.25/3.52     ( ( ( l1_pre_topc @ A ) & 
% 3.25/3.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.25/3.52       ( m1_subset_1 @
% 3.25/3.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.25/3.52  thf('5', plain,
% 3.25/3.52      (![X8 : $i, X9 : $i]:
% 3.25/3.52         (~ (l1_pre_topc @ X8)
% 3.25/3.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 3.25/3.52          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 3.25/3.52             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 3.25/3.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.25/3.52  thf('6', plain,
% 3.25/3.52      (((m1_subset_1 @ 
% 3.25/3.52         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.25/3.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.25/3.52        | ~ (l1_pre_topc @ sk_A))),
% 3.25/3.52      inference('sup-', [status(thm)], ['4', '5'])).
% 3.25/3.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('8', plain,
% 3.25/3.52      ((m1_subset_1 @ 
% 3.25/3.52        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.25/3.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('demod', [status(thm)], ['6', '7'])).
% 3.25/3.52  thf(t42_subset_1, axiom,
% 3.25/3.52    (![A:$i,B:$i]:
% 3.25/3.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.25/3.52       ( ![C:$i]:
% 3.25/3.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.25/3.52           ( r1_tarski @
% 3.25/3.52             ( k3_subset_1 @ A @ B ) @ 
% 3.25/3.52             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.25/3.52  thf('9', plain,
% 3.25/3.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.25/3.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.25/3.52          | (r1_tarski @ (k3_subset_1 @ X6 @ X7) @ 
% 3.25/3.52             (k3_subset_1 @ X6 @ (k9_subset_1 @ X6 @ X7 @ X5)))
% 3.25/3.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 3.25/3.52      inference('cnf', [status(esa)], [t42_subset_1])).
% 3.25/3.52  thf('10', plain,
% 3.25/3.52      (![X0 : $i]:
% 3.25/3.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.25/3.52          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 3.25/3.52             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.25/3.52              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 3.25/3.52               (k2_pre_topc @ sk_A @ 
% 3.25/3.52                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 3.25/3.52      inference('sup-', [status(thm)], ['8', '9'])).
% 3.25/3.52  thf('11', plain,
% 3.25/3.52      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.25/3.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.25/3.52         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.25/3.52          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.25/3.52      inference('sup-', [status(thm)], ['1', '10'])).
% 3.25/3.52  thf('12', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf(d2_tops_1, axiom,
% 3.25/3.52    (![A:$i]:
% 3.25/3.52     ( ( l1_pre_topc @ A ) =>
% 3.25/3.52       ( ![B:$i]:
% 3.25/3.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.25/3.52           ( ( k2_tops_1 @ A @ B ) =
% 3.25/3.52             ( k9_subset_1 @
% 3.25/3.52               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.25/3.52               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 3.25/3.52  thf('13', plain,
% 3.25/3.52      (![X12 : $i, X13 : $i]:
% 3.25/3.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.25/3.52          | ((k2_tops_1 @ X13 @ X12)
% 3.25/3.52              = (k9_subset_1 @ (u1_struct_0 @ X13) @ 
% 3.25/3.52                 (k2_pre_topc @ X13 @ X12) @ 
% 3.25/3.52                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 3.25/3.52          | ~ (l1_pre_topc @ X13))),
% 3.25/3.52      inference('cnf', [status(esa)], [d2_tops_1])).
% 3.25/3.52  thf('14', plain,
% 3.25/3.52      ((~ (l1_pre_topc @ sk_A)
% 3.25/3.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.25/3.52            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.25/3.52               (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.25/3.52               (k2_pre_topc @ sk_A @ 
% 3.25/3.52                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.25/3.52      inference('sup-', [status(thm)], ['12', '13'])).
% 3.25/3.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('16', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf(t52_pre_topc, axiom,
% 3.25/3.52    (![A:$i]:
% 3.25/3.52     ( ( l1_pre_topc @ A ) =>
% 3.25/3.52       ( ![B:$i]:
% 3.25/3.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.25/3.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.25/3.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.25/3.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.25/3.52  thf('17', plain,
% 3.25/3.52      (![X10 : $i, X11 : $i]:
% 3.25/3.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.25/3.52          | ~ (v4_pre_topc @ X10 @ X11)
% 3.25/3.52          | ((k2_pre_topc @ X11 @ X10) = (X10))
% 3.25/3.52          | ~ (l1_pre_topc @ X11))),
% 3.25/3.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.25/3.52  thf('18', plain,
% 3.25/3.52      ((~ (l1_pre_topc @ sk_A)
% 3.25/3.52        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 3.25/3.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.25/3.52      inference('sup-', [status(thm)], ['16', '17'])).
% 3.25/3.52  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('20', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('21', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 3.25/3.52      inference('demod', [status(thm)], ['18', '19', '20'])).
% 3.25/3.52  thf('22', plain,
% 3.25/3.52      (((k2_tops_1 @ sk_A @ sk_B)
% 3.25/3.52         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.25/3.52            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.25/3.52      inference('demod', [status(thm)], ['14', '15', '21'])).
% 3.25/3.52  thf('23', plain,
% 3.25/3.52      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.25/3.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.25/3.52      inference('demod', [status(thm)], ['11', '22'])).
% 3.25/3.52  thf(t31_subset_1, axiom,
% 3.25/3.52    (![A:$i,B:$i]:
% 3.25/3.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.25/3.52       ( ![C:$i]:
% 3.25/3.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.25/3.52           ( ( r1_tarski @ B @ C ) <=>
% 3.25/3.52             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.25/3.52  thf('24', plain,
% 3.25/3.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.25/3.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 3.25/3.52          | ~ (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 3.25/3.52          | (r1_tarski @ X4 @ X2)
% 3.25/3.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 3.25/3.52      inference('cnf', [status(esa)], [t31_subset_1])).
% 3.25/3.52  thf('25', plain,
% 3.25/3.52      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.25/3.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.25/3.52        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.25/3.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.25/3.52      inference('sup-', [status(thm)], ['23', '24'])).
% 3.25/3.52  thf('26', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf(dt_k2_tops_1, axiom,
% 3.25/3.52    (![A:$i,B:$i]:
% 3.25/3.52     ( ( ( l1_pre_topc @ A ) & 
% 3.25/3.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.25/3.52       ( m1_subset_1 @
% 3.25/3.52         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.25/3.52  thf('27', plain,
% 3.25/3.52      (![X14 : $i, X15 : $i]:
% 3.25/3.52         (~ (l1_pre_topc @ X14)
% 3.25/3.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 3.25/3.52          | (m1_subset_1 @ (k2_tops_1 @ X14 @ X15) @ 
% 3.25/3.52             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 3.25/3.52      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.25/3.52  thf('28', plain,
% 3.25/3.52      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.25/3.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.25/3.52        | ~ (l1_pre_topc @ sk_A))),
% 3.25/3.52      inference('sup-', [status(thm)], ['26', '27'])).
% 3.25/3.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('30', plain,
% 3.25/3.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.25/3.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('demod', [status(thm)], ['28', '29'])).
% 3.25/3.52  thf('31', plain,
% 3.25/3.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.25/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.52  thf('32', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.25/3.52      inference('demod', [status(thm)], ['25', '30', '31'])).
% 3.25/3.52  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 3.25/3.52  
% 3.25/3.52  % SZS output end Refutation
% 3.25/3.52  
% 3.38/3.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
