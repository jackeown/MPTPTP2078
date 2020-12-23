%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3SrkFdwTyZ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:46 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  472 (1230 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v5_tops_1 @ X42 @ X43 )
      | ( X42
        = ( k2_pre_topc @ X43 @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X49 @ X48 ) @ X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('14',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ ( k2_pre_topc @ X47 @ X46 ) @ ( k1_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_pre_topc @ X40 @ ( k2_pre_topc @ X40 @ X41 ) )
        = ( k2_pre_topc @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('29',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('33',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','34','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['7','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3SrkFdwTyZ
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 133 iterations in 0.086s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.34/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.34/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.34/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.34/0.54  thf(t103_tops_1, conjecture,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( l1_pre_topc @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.54           ( ( v5_tops_1 @ B @ A ) =>
% 0.34/0.54             ( r1_tarski @
% 0.34/0.54               ( k2_tops_1 @ A @ B ) @ 
% 0.34/0.54               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.54    (~( ![A:$i]:
% 0.34/0.54        ( ( l1_pre_topc @ A ) =>
% 0.34/0.54          ( ![B:$i]:
% 0.34/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.54              ( ( v5_tops_1 @ B @ A ) =>
% 0.34/0.54                ( r1_tarski @
% 0.34/0.54                  ( k2_tops_1 @ A @ B ) @ 
% 0.34/0.54                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.34/0.54  thf('0', plain,
% 0.34/0.54      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.54          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('1', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(d7_tops_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( l1_pre_topc @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.54           ( ( v5_tops_1 @ B @ A ) <=>
% 0.34/0.54             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf('2', plain,
% 0.34/0.54      (![X42 : $i, X43 : $i]:
% 0.34/0.54         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.34/0.54          | ~ (v5_tops_1 @ X42 @ X43)
% 0.34/0.54          | ((X42) = (k2_pre_topc @ X43 @ (k1_tops_1 @ X43 @ X42)))
% 0.34/0.54          | ~ (l1_pre_topc @ X43))),
% 0.34/0.54      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.34/0.54  thf('3', plain,
% 0.34/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.54        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.34/0.54        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.34/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.54  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.34/0.54  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.34/0.54      inference('demod', [status(thm)], ['0', '6'])).
% 0.34/0.54  thf('8', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(t44_tops_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( l1_pre_topc @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.34/0.54  thf('9', plain,
% 0.34/0.54      (![X48 : $i, X49 : $i]:
% 0.34/0.54         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.34/0.54          | (r1_tarski @ (k1_tops_1 @ X49 @ X48) @ X48)
% 0.34/0.54          | ~ (l1_pre_topc @ X49))),
% 0.34/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.34/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.34/0.54  thf(t45_xboole_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_tarski @ A @ B ) =>
% 0.34/0.54       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.34/0.54  thf('13', plain,
% 0.34/0.54      (![X4 : $i, X5 : $i]:
% 0.34/0.54         (((X5) = (k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))
% 0.34/0.54          | ~ (r1_tarski @ X4 @ X5))),
% 0.34/0.54      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.34/0.54  thf('14', plain,
% 0.34/0.54      (((sk_B)
% 0.34/0.54         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.54            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.34/0.54  thf('15', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.34/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.34/0.54  thf(t7_xboole_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.34/0.54  thf('17', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('18', plain,
% 0.34/0.54      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.34/0.54      inference('sup+', [status(thm)], ['14', '17'])).
% 0.34/0.54  thf('19', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(l78_tops_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( l1_pre_topc @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.34/0.54             ( k7_subset_1 @
% 0.34/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.34/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.34/0.54  thf('20', plain,
% 0.34/0.54      (![X46 : $i, X47 : $i]:
% 0.34/0.54         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.34/0.54          | ((k2_tops_1 @ X47 @ X46)
% 0.34/0.54              = (k7_subset_1 @ (u1_struct_0 @ X47) @ 
% 0.34/0.54                 (k2_pre_topc @ X47 @ X46) @ (k1_tops_1 @ X47 @ X46)))
% 0.34/0.54          | ~ (l1_pre_topc @ X47))),
% 0.34/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.34/0.54  thf('21', plain,
% 0.34/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.54  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('23', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(dt_k1_tops_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.34/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.54       ( m1_subset_1 @
% 0.34/0.54         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.54  thf('24', plain,
% 0.34/0.54      (![X44 : $i, X45 : $i]:
% 0.34/0.54         (~ (l1_pre_topc @ X44)
% 0.34/0.54          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.34/0.54          | (m1_subset_1 @ (k1_tops_1 @ X44 @ X45) @ 
% 0.34/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 0.34/0.54      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.34/0.54  thf('25', plain,
% 0.34/0.54      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.54  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.54  thf(projectivity_k2_pre_topc, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.34/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.54       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.34/0.54         ( k2_pre_topc @ A @ B ) ) ))).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      (![X40 : $i, X41 : $i]:
% 0.34/0.54         (~ (l1_pre_topc @ X40)
% 0.34/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.34/0.54          | ((k2_pre_topc @ X40 @ (k2_pre_topc @ X40 @ X41))
% 0.34/0.54              = (k2_pre_topc @ X40 @ X41)))),
% 0.34/0.54      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.34/0.54  thf('29', plain,
% 0.34/0.54      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.34/0.54          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.34/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.54  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('31', plain,
% 0.34/0.54      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.34/0.54         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.34/0.54  thf('33', plain,
% 0.34/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.34/0.54  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.34/0.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.34/0.54  thf('35', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i]:
% 0.34/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.34/0.54  thf('36', plain,
% 0.34/0.54      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.34/0.54         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.34/0.54          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 0.34/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.34/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.34/0.54  thf('38', plain,
% 0.34/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.54         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.54      inference('demod', [status(thm)], ['21', '22', '34', '37'])).
% 0.34/0.54  thf('39', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.34/0.54      inference('demod', [status(thm)], ['18', '38'])).
% 0.34/0.54  thf('40', plain, ($false), inference('demod', [status(thm)], ['7', '39'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.34/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
