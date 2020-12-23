%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oag8M091U1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:45 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
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

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ ( k1_tops_1 @ X18 @ X17 ) )
        = ( k2_tops_1 @ X18 @ X17 ) )
      | ~ ( v5_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oag8M091U1
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:04:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.27/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.45  % Solved by: fo/fo7.sh
% 1.27/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.45  % done 1220 iterations in 0.985s
% 1.27/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.45  % SZS output start Refutation
% 1.27/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.27/1.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.27/1.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.27/1.45  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.27/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.27/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.27/1.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.27/1.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.45  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.27/1.45  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.27/1.45  thf(t103_tops_1, conjecture,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( l1_pre_topc @ A ) =>
% 1.27/1.45       ( ![B:$i]:
% 1.27/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.45           ( ( v5_tops_1 @ B @ A ) =>
% 1.27/1.45             ( r1_tarski @
% 1.27/1.45               ( k2_tops_1 @ A @ B ) @ 
% 1.27/1.45               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.27/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.45    (~( ![A:$i]:
% 1.27/1.45        ( ( l1_pre_topc @ A ) =>
% 1.27/1.45          ( ![B:$i]:
% 1.27/1.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.45              ( ( v5_tops_1 @ B @ A ) =>
% 1.27/1.45                ( r1_tarski @
% 1.27/1.45                  ( k2_tops_1 @ A @ B ) @ 
% 1.27/1.45                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.27/1.45    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.27/1.45  thf('0', plain,
% 1.27/1.45      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('1', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(dt_k2_tops_1, axiom,
% 1.27/1.45    (![A:$i,B:$i]:
% 1.27/1.45     ( ( ( l1_pre_topc @ A ) & 
% 1.27/1.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.27/1.45       ( m1_subset_1 @
% 1.27/1.45         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.27/1.45  thf('2', plain,
% 1.27/1.45      (![X15 : $i, X16 : $i]:
% 1.27/1.45         (~ (l1_pre_topc @ X15)
% 1.27/1.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.27/1.45          | (m1_subset_1 @ (k2_tops_1 @ X15 @ X16) @ 
% 1.27/1.45             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.27/1.45      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.27/1.45  thf('3', plain,
% 1.27/1.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.45        | ~ (l1_pre_topc @ sk_A))),
% 1.27/1.45      inference('sup-', [status(thm)], ['1', '2'])).
% 1.27/1.45  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('5', plain,
% 1.27/1.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('demod', [status(thm)], ['3', '4'])).
% 1.27/1.45  thf('6', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(dt_k1_tops_1, axiom,
% 1.27/1.45    (![A:$i,B:$i]:
% 1.27/1.45     ( ( ( l1_pre_topc @ A ) & 
% 1.27/1.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.27/1.45       ( m1_subset_1 @
% 1.27/1.45         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.27/1.45  thf('7', plain,
% 1.27/1.45      (![X13 : $i, X14 : $i]:
% 1.27/1.45         (~ (l1_pre_topc @ X13)
% 1.27/1.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.27/1.45          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 1.27/1.45             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 1.27/1.45      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.27/1.45  thf('8', plain,
% 1.27/1.45      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.45        | ~ (l1_pre_topc @ sk_A))),
% 1.27/1.45      inference('sup-', [status(thm)], ['6', '7'])).
% 1.27/1.45  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('10', plain,
% 1.27/1.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('demod', [status(thm)], ['8', '9'])).
% 1.27/1.45  thf(redefinition_k4_subset_1, axiom,
% 1.27/1.45    (![A:$i,B:$i,C:$i]:
% 1.27/1.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.27/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.27/1.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.27/1.45  thf('11', plain,
% 1.27/1.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.27/1.45         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.27/1.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 1.27/1.45          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.27/1.45  thf('12', plain,
% 1.27/1.45      (![X0 : $i]:
% 1.27/1.45         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.27/1.45            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.27/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.27/1.45      inference('sup-', [status(thm)], ['10', '11'])).
% 1.27/1.45  thf('13', plain,
% 1.27/1.45      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45         (k2_tops_1 @ sk_A @ sk_B))
% 1.27/1.45         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['5', '12'])).
% 1.27/1.45  thf(commutativity_k2_xboole_0, axiom,
% 1.27/1.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.27/1.45  thf('14', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.27/1.45  thf('15', plain,
% 1.27/1.45      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45         (k2_tops_1 @ sk_A @ sk_B))
% 1.27/1.45         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('demod', [status(thm)], ['13', '14'])).
% 1.27/1.45  thf('16', plain,
% 1.27/1.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('demod', [status(thm)], ['8', '9'])).
% 1.27/1.45  thf(t65_tops_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( l1_pre_topc @ A ) =>
% 1.27/1.45       ( ![B:$i]:
% 1.27/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.45           ( ( k2_pre_topc @ A @ B ) =
% 1.27/1.45             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.27/1.45  thf('17', plain,
% 1.27/1.45      (![X19 : $i, X20 : $i]:
% 1.27/1.45         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.27/1.45          | ((k2_pre_topc @ X20 @ X19)
% 1.27/1.45              = (k4_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 1.27/1.45                 (k2_tops_1 @ X20 @ X19)))
% 1.27/1.45          | ~ (l1_pre_topc @ X20))),
% 1.27/1.45      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.27/1.45  thf('18', plain,
% 1.27/1.45      ((~ (l1_pre_topc @ sk_A)
% 1.27/1.45        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.27/1.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.27/1.45               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.45               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.27/1.45      inference('sup-', [status(thm)], ['16', '17'])).
% 1.27/1.45  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('20', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(t102_tops_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( l1_pre_topc @ A ) =>
% 1.27/1.45       ( ![B:$i]:
% 1.27/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.46           ( ( v5_tops_1 @ B @ A ) =>
% 1.27/1.46             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 1.27/1.46               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.27/1.46  thf('21', plain,
% 1.27/1.46      (![X17 : $i, X18 : $i]:
% 1.27/1.46         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.27/1.46          | ((k2_tops_1 @ X18 @ (k1_tops_1 @ X18 @ X17))
% 1.27/1.46              = (k2_tops_1 @ X18 @ X17))
% 1.27/1.46          | ~ (v5_tops_1 @ X17 @ X18)
% 1.27/1.46          | ~ (l1_pre_topc @ X18))),
% 1.27/1.46      inference('cnf', [status(esa)], [t102_tops_1])).
% 1.27/1.46  thf('22', plain,
% 1.27/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.27/1.46        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 1.27/1.46        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.27/1.46            = (k2_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.27/1.46  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('24', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('25', plain,
% 1.27/1.46      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.27/1.46         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.27/1.46      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.27/1.46  thf('26', plain,
% 1.27/1.46      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.27/1.46         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.46            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.46      inference('demod', [status(thm)], ['18', '19', '25'])).
% 1.27/1.46  thf('27', plain,
% 1.27/1.46      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.27/1.46         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.46      inference('sup+', [status(thm)], ['15', '26'])).
% 1.27/1.46  thf(t7_xboole_1, axiom,
% 1.27/1.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.46  thf('28', plain,
% 1.27/1.46      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.27/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.27/1.46  thf('29', plain,
% 1.27/1.46      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.27/1.46        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.27/1.46      inference('sup+', [status(thm)], ['27', '28'])).
% 1.27/1.46  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 1.27/1.46  
% 1.27/1.46  % SZS output end Refutation
% 1.27/1.46  
% 1.27/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
