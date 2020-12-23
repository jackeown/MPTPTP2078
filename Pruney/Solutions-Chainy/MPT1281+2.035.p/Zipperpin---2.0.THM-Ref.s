%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XS4rBAW4q5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 112 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  511 (1279 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v5_tops_1 @ X13 @ X14 )
      | ( X13
        = ( k2_pre_topc @ X14 @ ( k1_tops_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_tops_1 @ X16 @ X15 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ ( k2_pre_topc @ X9 @ X10 ) )
        = ( k2_pre_topc @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('28',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('32',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','33','36'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['7','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XS4rBAW4q5
% 0.16/0.36  % Computer   : n019.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:29:08 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 89 iterations in 0.065s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.54  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.37/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.54  thf(t103_tops_1, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_pre_topc @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ( v5_tops_1 @ B @ A ) =>
% 0.37/0.54             ( r1_tarski @
% 0.37/0.54               ( k2_tops_1 @ A @ B ) @ 
% 0.37/0.54               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( l1_pre_topc @ A ) =>
% 0.37/0.54          ( ![B:$i]:
% 0.37/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54              ( ( v5_tops_1 @ B @ A ) =>
% 0.37/0.54                ( r1_tarski @
% 0.37/0.54                  ( k2_tops_1 @ A @ B ) @ 
% 0.37/0.54                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.54          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d7_tops_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_pre_topc @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ( v5_tops_1 @ B @ A ) <=>
% 0.37/0.54             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.54          | ~ (v5_tops_1 @ X13 @ X14)
% 0.37/0.54          | ((X13) = (k2_pre_topc @ X14 @ (k1_tops_1 @ X14 @ X13)))
% 0.37/0.54          | ~ (l1_pre_topc @ X14))),
% 0.37/0.54      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.54        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.54        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.54  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '6'])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(l78_tops_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_pre_topc @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.54             ( k7_subset_1 @
% 0.37/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.37/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.54          | ((k2_tops_1 @ X16 @ X15)
% 0.37/0.54              = (k7_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.37/0.54                 (k2_pre_topc @ X16 @ X15) @ (k1_tops_1 @ X16 @ X15)))
% 0.37/0.54          | ~ (l1_pre_topc @ X16))),
% 0.37/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(dt_k3_subset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]:
% 0.37/0.54         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.54  thf(dt_k2_pre_topc, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.54       ( m1_subset_1 @
% 0.37/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X7 : $i, X8 : $i]:
% 0.37/0.54         (~ (l1_pre_topc @ X7)
% 0.37/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.54          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.37/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (((m1_subset_1 @ 
% 0.37/0.54         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      ((m1_subset_1 @ 
% 0.37/0.54        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]:
% 0.37/0.54         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.37/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      ((m1_subset_1 @ 
% 0.37/0.54        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.54         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.37/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d1_tops_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_pre_topc @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.54             ( k3_subset_1 @
% 0.37/0.54               ( u1_struct_0 @ A ) @ 
% 0.37/0.54               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.54          | ((k1_tops_1 @ X12 @ X11)
% 0.37/0.54              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.37/0.54                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 0.37/0.54          | ~ (l1_pre_topc @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.54        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.54            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.54               (k2_pre_topc @ sk_A @ 
% 0.37/0.54                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.54         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.54            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.54  thf(projectivity_k2_pre_topc, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.54       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.37/0.54         ( k2_pre_topc @ A @ B ) ) ))).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i]:
% 0.37/0.54         (~ (l1_pre_topc @ X9)
% 0.37/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.37/0.54          | ((k2_pre_topc @ X9 @ (k2_pre_topc @ X9 @ X10))
% 0.37/0.54              = (k2_pre_topc @ X9 @ X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.54          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.54         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.54  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.37/0.54          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.37/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.54         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('demod', [status(thm)], ['10', '11', '33', '36'])).
% 0.37/0.54  thf(t36_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.54  thf('39', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.37/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.54  thf('40', plain, ($false), inference('demod', [status(thm)], ['7', '39'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
