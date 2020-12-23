%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h3yYSobRb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  389 ( 653 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k3_tarski @ ( k2_tarski @ X33 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','10','21'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h3yYSobRb
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 82 iterations in 0.054s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(t69_tops_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.50             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( l1_pre_topc @ A ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50              ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.50                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.19/0.50  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t65_tops_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ( k2_pre_topc @ A @ B ) =
% 0.19/0.50             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X40 : $i, X41 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.19/0.50          | ((k2_pre_topc @ X41 @ X40)
% 0.19/0.50              = (k4_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 0.19/0.50                 (k2_tops_1 @ X41 @ X40)))
% 0.19/0.50          | ~ (l1_pre_topc @ X41))),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.50        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.50            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.50               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t52_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.19/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.19/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X36 : $i, X37 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.19/0.50          | ~ (v4_pre_topc @ X36 @ X37)
% 0.19/0.50          | ((k2_pre_topc @ X37 @ X36) = (X36))
% 0.19/0.50          | ~ (l1_pre_topc @ X37))),
% 0.19/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.50        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.19/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_k2_tops_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.50       ( m1_subset_1 @
% 0.19/0.50         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X38 : $i, X39 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ X38)
% 0.19/0.50          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.19/0.50          | (m1_subset_1 @ (k2_tops_1 @ X38 @ X39) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.19/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 0.19/0.50          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.50  thf(l51_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.19/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 0.19/0.50          | ((k4_subset_1 @ X34 @ X33 @ X35)
% 0.19/0.50              = (k3_tarski @ (k2_tarski @ X33 @ X35))))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.50            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.50         = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4', '10', '21'])).
% 0.19/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.19/0.50           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.19/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.50  thf(t7_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i]:
% 0.19/0.50         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X2 @ X3)))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['26', '29'])).
% 0.19/0.50  thf('31', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.50      inference('sup+', [status(thm)], ['22', '30'])).
% 0.19/0.50  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
