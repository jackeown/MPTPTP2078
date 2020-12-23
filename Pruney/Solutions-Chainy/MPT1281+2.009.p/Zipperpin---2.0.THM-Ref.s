%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TcWZLyaPS9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:45 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  430 ( 854 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X19 ) )
        = ( k2_tops_1 @ X20 @ X19 ) )
      | ~ ( v5_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TcWZLyaPS9
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.88/3.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.88/3.09  % Solved by: fo/fo7.sh
% 2.88/3.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.88/3.09  % done 4827 iterations in 2.639s
% 2.88/3.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.88/3.09  % SZS output start Refutation
% 2.88/3.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.88/3.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.88/3.09  thf(sk_A_type, type, sk_A: $i).
% 2.88/3.09  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.88/3.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.88/3.09  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.88/3.09  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.88/3.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.88/3.09  thf(sk_B_type, type, sk_B: $i).
% 2.88/3.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.88/3.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.88/3.09  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 2.88/3.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.88/3.09  thf(t103_tops_1, conjecture,
% 2.88/3.09    (![A:$i]:
% 2.88/3.09     ( ( l1_pre_topc @ A ) =>
% 2.88/3.09       ( ![B:$i]:
% 2.88/3.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.88/3.09           ( ( v5_tops_1 @ B @ A ) =>
% 2.88/3.09             ( r1_tarski @
% 2.88/3.09               ( k2_tops_1 @ A @ B ) @ 
% 2.88/3.09               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.88/3.09  thf(zf_stmt_0, negated_conjecture,
% 2.88/3.09    (~( ![A:$i]:
% 2.88/3.09        ( ( l1_pre_topc @ A ) =>
% 2.88/3.09          ( ![B:$i]:
% 2.88/3.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.88/3.09              ( ( v5_tops_1 @ B @ A ) =>
% 2.88/3.09                ( r1_tarski @
% 2.88/3.09                  ( k2_tops_1 @ A @ B ) @ 
% 2.88/3.09                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.88/3.09    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 2.88/3.09  thf('0', plain,
% 2.88/3.09      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('1', plain,
% 2.88/3.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf(dt_k2_tops_1, axiom,
% 2.88/3.09    (![A:$i,B:$i]:
% 2.88/3.09     ( ( ( l1_pre_topc @ A ) & 
% 2.88/3.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.88/3.09       ( m1_subset_1 @
% 2.88/3.09         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.88/3.09  thf('2', plain,
% 2.88/3.09      (![X17 : $i, X18 : $i]:
% 2.88/3.09         (~ (l1_pre_topc @ X17)
% 2.88/3.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 2.88/3.09          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 2.88/3.09             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 2.88/3.09      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.88/3.09  thf('3', plain,
% 2.88/3.09      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.88/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.88/3.09      inference('sup-', [status(thm)], ['1', '2'])).
% 2.88/3.09  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('5', plain,
% 2.88/3.09      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.88/3.09  thf('6', plain,
% 2.88/3.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf(dt_k1_tops_1, axiom,
% 2.88/3.09    (![A:$i,B:$i]:
% 2.88/3.09     ( ( ( l1_pre_topc @ A ) & 
% 2.88/3.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.88/3.09       ( m1_subset_1 @
% 2.88/3.09         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.88/3.09  thf('7', plain,
% 2.88/3.09      (![X15 : $i, X16 : $i]:
% 2.88/3.09         (~ (l1_pre_topc @ X15)
% 2.88/3.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.88/3.09          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 2.88/3.09             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 2.88/3.09      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.88/3.09  thf('8', plain,
% 2.88/3.09      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.88/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.88/3.09      inference('sup-', [status(thm)], ['6', '7'])).
% 2.88/3.09  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('10', plain,
% 2.88/3.09      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('demod', [status(thm)], ['8', '9'])).
% 2.88/3.09  thf(redefinition_k4_subset_1, axiom,
% 2.88/3.09    (![A:$i,B:$i,C:$i]:
% 2.88/3.09     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.88/3.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.88/3.09       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.88/3.09  thf('11', plain,
% 2.88/3.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.88/3.09         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.88/3.09          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.88/3.09          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.88/3.09      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.88/3.09  thf('12', plain,
% 2.88/3.09      (![X0 : $i]:
% 2.88/3.09         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.88/3.09            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 2.88/3.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.88/3.09      inference('sup-', [status(thm)], ['10', '11'])).
% 2.88/3.09  thf('13', plain,
% 2.88/3.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09         (k2_tops_1 @ sk_A @ sk_B))
% 2.88/3.09         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('sup-', [status(thm)], ['5', '12'])).
% 2.88/3.09  thf(commutativity_k2_xboole_0, axiom,
% 2.88/3.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.88/3.09  thf('14', plain,
% 2.88/3.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.88/3.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.88/3.09  thf('15', plain,
% 2.88/3.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09         (k2_tops_1 @ sk_A @ sk_B))
% 2.88/3.09         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('demod', [status(thm)], ['13', '14'])).
% 2.88/3.09  thf('16', plain,
% 2.88/3.09      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('demod', [status(thm)], ['8', '9'])).
% 2.88/3.09  thf(t65_tops_1, axiom,
% 2.88/3.09    (![A:$i]:
% 2.88/3.09     ( ( l1_pre_topc @ A ) =>
% 2.88/3.09       ( ![B:$i]:
% 2.88/3.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.88/3.09           ( ( k2_pre_topc @ A @ B ) =
% 2.88/3.09             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.88/3.09  thf('17', plain,
% 2.88/3.09      (![X21 : $i, X22 : $i]:
% 2.88/3.09         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.88/3.09          | ((k2_pre_topc @ X22 @ X21)
% 2.88/3.09              = (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 2.88/3.09                 (k2_tops_1 @ X22 @ X21)))
% 2.88/3.09          | ~ (l1_pre_topc @ X22))),
% 2.88/3.09      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.88/3.09  thf('18', plain,
% 2.88/3.09      ((~ (l1_pre_topc @ sk_A)
% 2.88/3.09        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.88/3.09            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.88/3.09               (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.88/3.09      inference('sup-', [status(thm)], ['16', '17'])).
% 2.88/3.09  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('20', plain,
% 2.88/3.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf(t102_tops_1, axiom,
% 2.88/3.09    (![A:$i]:
% 2.88/3.09     ( ( l1_pre_topc @ A ) =>
% 2.88/3.09       ( ![B:$i]:
% 2.88/3.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.88/3.09           ( ( v5_tops_1 @ B @ A ) =>
% 2.88/3.09             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 2.88/3.09               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.88/3.09  thf('21', plain,
% 2.88/3.09      (![X19 : $i, X20 : $i]:
% 2.88/3.09         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.88/3.09          | ((k2_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X19))
% 2.88/3.09              = (k2_tops_1 @ X20 @ X19))
% 2.88/3.09          | ~ (v5_tops_1 @ X19 @ X20)
% 2.88/3.09          | ~ (l1_pre_topc @ X20))),
% 2.88/3.09      inference('cnf', [status(esa)], [t102_tops_1])).
% 2.88/3.09  thf('22', plain,
% 2.88/3.09      ((~ (l1_pre_topc @ sk_A)
% 2.88/3.09        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 2.88/3.09        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.88/3.09            = (k2_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('sup-', [status(thm)], ['20', '21'])).
% 2.88/3.09  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('24', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 2.88/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.09  thf('25', plain,
% 2.88/3.09      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.88/3.09         = (k2_tops_1 @ sk_A @ sk_B))),
% 2.88/3.09      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.88/3.09  thf('26', plain,
% 2.88/3.09      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.88/3.09         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('demod', [status(thm)], ['18', '19', '25'])).
% 2.88/3.09  thf('27', plain,
% 2.88/3.09      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.88/3.09         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('sup+', [status(thm)], ['15', '26'])).
% 2.88/3.09  thf(t7_xboole_1, axiom,
% 2.88/3.09    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.88/3.09  thf('28', plain,
% 2.88/3.09      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 2.88/3.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.88/3.09  thf('29', plain,
% 2.88/3.09      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.88/3.09        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.88/3.09      inference('sup+', [status(thm)], ['27', '28'])).
% 2.88/3.09  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 2.88/3.09  
% 2.88/3.09  % SZS output end Refutation
% 2.88/3.09  
% 2.88/3.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
