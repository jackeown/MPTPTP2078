%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JK9AoFpOsV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 100 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  501 (1165 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('15',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_subset_1 @ X11 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ ( k1_tops_1 @ X21 @ X20 ) )
        = ( k2_tops_1 @ X21 @ X20 ) )
      | ~ ( v5_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','28'])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JK9AoFpOsV
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.27  % Solved by: fo/fo7.sh
% 1.05/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.27  % done 542 iterations in 0.815s
% 1.05/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.27  % SZS output start Refutation
% 1.05/1.27  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.05/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.27  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.05/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.27  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.05/1.27  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.05/1.27  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.05/1.27  thf(t103_tops_1, conjecture,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( l1_pre_topc @ A ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27           ( ( v5_tops_1 @ B @ A ) =>
% 1.05/1.27             ( r1_tarski @
% 1.05/1.27               ( k2_tops_1 @ A @ B ) @ 
% 1.05/1.27               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.27    (~( ![A:$i]:
% 1.05/1.27        ( ( l1_pre_topc @ A ) =>
% 1.05/1.27          ( ![B:$i]:
% 1.05/1.27            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27              ( ( v5_tops_1 @ B @ A ) =>
% 1.05/1.27                ( r1_tarski @
% 1.05/1.27                  ( k2_tops_1 @ A @ B ) @ 
% 1.05/1.27                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.05/1.27    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.05/1.27  thf('0', plain,
% 1.05/1.27      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('1', plain,
% 1.05/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(dt_k1_tops_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( ( l1_pre_topc @ A ) & 
% 1.05/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.27       ( m1_subset_1 @
% 1.05/1.27         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.05/1.27  thf('2', plain,
% 1.05/1.27      (![X16 : $i, X17 : $i]:
% 1.05/1.27         (~ (l1_pre_topc @ X16)
% 1.05/1.27          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.05/1.27          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 1.05/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 1.05/1.27      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.05/1.27  thf('3', plain,
% 1.05/1.27      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.27      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.27  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('5', plain,
% 1.05/1.27      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['3', '4'])).
% 1.05/1.27  thf('6', plain,
% 1.05/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(dt_k2_tops_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]:
% 1.05/1.27     ( ( ( l1_pre_topc @ A ) & 
% 1.05/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.27       ( m1_subset_1 @
% 1.05/1.27         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.05/1.27  thf('7', plain,
% 1.05/1.27      (![X18 : $i, X19 : $i]:
% 1.05/1.27         (~ (l1_pre_topc @ X18)
% 1.05/1.27          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.05/1.27          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 1.05/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.05/1.27      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.05/1.27  thf('8', plain,
% 1.05/1.27      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.27      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.27  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('10', plain,
% 1.05/1.27      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.05/1.27  thf(redefinition_k4_subset_1, axiom,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.27       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.27  thf('11', plain,
% 1.05/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.05/1.27          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.05/1.27          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.05/1.27      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.27  thf('12', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.05/1.27            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.05/1.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.27      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.27  thf('13', plain,
% 1.05/1.27      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27         (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['5', '12'])).
% 1.05/1.27  thf('14', plain,
% 1.05/1.27      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.05/1.27  thf('15', plain,
% 1.05/1.27      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['3', '4'])).
% 1.05/1.27  thf(commutativity_k4_subset_1, axiom,
% 1.05/1.27    (![A:$i,B:$i,C:$i]:
% 1.05/1.27     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.27       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 1.05/1.27  thf('16', plain,
% 1.05/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.05/1.27          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 1.05/1.27          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k4_subset_1 @ X11 @ X12 @ X10)))),
% 1.05/1.27      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 1.05/1.27  thf('17', plain,
% 1.05/1.27      (![X0 : $i]:
% 1.05/1.27         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.05/1.27            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.05/1.27               (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.27      inference('sup-', [status(thm)], ['15', '16'])).
% 1.05/1.27  thf('18', plain,
% 1.05/1.27      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27         (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['14', '17'])).
% 1.05/1.27  thf('19', plain,
% 1.05/1.27      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('demod', [status(thm)], ['3', '4'])).
% 1.05/1.27  thf(t65_tops_1, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( l1_pre_topc @ A ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27           ( ( k2_pre_topc @ A @ B ) =
% 1.05/1.27             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.27  thf('20', plain,
% 1.05/1.27      (![X22 : $i, X23 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.05/1.27          | ((k2_pre_topc @ X23 @ X22)
% 1.05/1.27              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 1.05/1.27                 (k2_tops_1 @ X23 @ X22)))
% 1.05/1.27          | ~ (l1_pre_topc @ X23))),
% 1.05/1.27      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.05/1.27  thf('21', plain,
% 1.05/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.27        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.27               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.27      inference('sup-', [status(thm)], ['19', '20'])).
% 1.05/1.27  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('23', plain,
% 1.05/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf(t102_tops_1, axiom,
% 1.05/1.27    (![A:$i]:
% 1.05/1.27     ( ( l1_pre_topc @ A ) =>
% 1.05/1.27       ( ![B:$i]:
% 1.05/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.27           ( ( v5_tops_1 @ B @ A ) =>
% 1.05/1.27             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 1.05/1.27               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.27  thf('24', plain,
% 1.05/1.27      (![X20 : $i, X21 : $i]:
% 1.05/1.27         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.05/1.27          | ((k2_tops_1 @ X21 @ (k1_tops_1 @ X21 @ X20))
% 1.05/1.27              = (k2_tops_1 @ X21 @ X20))
% 1.05/1.27          | ~ (v5_tops_1 @ X20 @ X21)
% 1.05/1.27          | ~ (l1_pre_topc @ X21))),
% 1.05/1.27      inference('cnf', [status(esa)], [t102_tops_1])).
% 1.05/1.27  thf('25', plain,
% 1.05/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.27        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 1.05/1.27        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27            = (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup-', [status(thm)], ['23', '24'])).
% 1.05/1.27  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('27', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.05/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.27  thf('28', plain,
% 1.05/1.27      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.05/1.27      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.05/1.27  thf('29', plain,
% 1.05/1.27      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('demod', [status(thm)], ['21', '22', '28'])).
% 1.05/1.27  thf('30', plain,
% 1.05/1.27      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup+', [status(thm)], ['18', '29'])).
% 1.05/1.27  thf('31', plain,
% 1.05/1.27      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.05/1.27         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup+', [status(thm)], ['13', '30'])).
% 1.05/1.27  thf(t7_xboole_1, axiom,
% 1.05/1.27    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.27  thf('32', plain,
% 1.05/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.05/1.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.05/1.27  thf('33', plain,
% 1.05/1.27      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.27        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.27      inference('sup+', [status(thm)], ['31', '32'])).
% 1.05/1.27  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 1.05/1.27  
% 1.05/1.27  % SZS output end Refutation
% 1.05/1.27  
% 1.05/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
