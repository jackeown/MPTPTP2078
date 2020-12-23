%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJxfqDmLuo

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:48 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 123 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  548 (1319 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v5_tops_1 @ X19 @ X20 )
      | ( X19
        = ( k2_pre_topc @ X20 @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ ( k2_pre_topc @ X15 @ X16 ) )
        = ( k2_pre_topc @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('19',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('23',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','24','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['32','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['7','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJxfqDmLuo
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 772 iterations in 0.510s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(t103_tops_1, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v5_tops_1 @ B @ A ) =>
% 0.76/0.96             ( r1_tarski @
% 0.76/0.96               ( k2_tops_1 @ A @ B ) @ 
% 0.76/0.96               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_pre_topc @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96              ( ( v5_tops_1 @ B @ A ) =>
% 0.76/0.96                ( r1_tarski @
% 0.76/0.96                  ( k2_tops_1 @ A @ B ) @ 
% 0.76/0.96                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.96          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d7_tops_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v5_tops_1 @ B @ A ) <=>
% 0.76/0.96             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X19 : $i, X20 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.76/0.96          | ~ (v5_tops_1 @ X19 @ X20)
% 0.76/0.96          | ((X19) = (k2_pre_topc @ X20 @ (k1_tops_1 @ X20 @ X19)))
% 0.76/0.96          | ~ (l1_pre_topc @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.96        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.76/0.96  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '6'])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d2_tops_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( k2_tops_1 @ A @ B ) =
% 0.76/0.96             ( k9_subset_1 @
% 0.76/0.96               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.76/0.96               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.76/0.96          | ((k2_tops_1 @ X18 @ X17)
% 0.76/0.96              = (k9_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.76/0.96                 (k2_pre_topc @ X18 @ X17) @ 
% 0.76/0.96                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.76/0.96          | ~ (l1_pre_topc @ X18))),
% 0.76/0.96      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.96        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.96            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.76/0.96               (k2_pre_topc @ sk_A @ 
% 0.76/0.96                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.96         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.76/0.96            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['10', '11'])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(dt_k1_tops_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.96       ( m1_subset_1 @
% 0.76/0.96         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X21 : $i, X22 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ X21)
% 0.76/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/0.96          | (m1_subset_1 @ (k1_tops_1 @ X21 @ X22) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.96  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.96  thf(projectivity_k2_pre_topc, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.96       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.76/0.96         ( k2_pre_topc @ A @ B ) ) ))).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (![X15 : $i, X16 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ X15)
% 0.76/0.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.76/0.96          | ((k2_pre_topc @ X15 @ (k2_pre_topc @ X15 @ X16))
% 0.76/0.96              = (k2_pre_topc @ X15 @ X16)))),
% 0.76/0.96      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.76/0.96         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.76/0.96  thf('24', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(commutativity_k9_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.96         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.76/0.96          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.96         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.76/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.96           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k3_xboole_0 @ X0 @ sk_B)
% 0.76/0.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['27', '30'])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (((k2_tops_1 @ sk_A @ sk_B)
% 0.76/0.96         = (k3_xboole_0 @ 
% 0.76/0.96            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.76/0.96            sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['12', '24', '31'])).
% 0.76/0.96  thf(d10_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.96  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.96      inference('simplify', [status(thm)], ['33'])).
% 0.76/0.96  thf(t3_subset, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      (![X12 : $i, X14 : $i]:
% 0.76/0.96         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.96  thf(dt_k9_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.76/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      (![X12 : $i, X13 : $i]:
% 0.76/0.96         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.76/0.96      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.96  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.96  thf('42', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.96         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.76/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.76/0.96      inference('demod', [status(thm)], ['40', '43'])).
% 0.76/0.96  thf('45', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.76/0.96      inference('sup+', [status(thm)], ['32', '44'])).
% 0.76/0.96  thf('46', plain, ($false), inference('demod', [status(thm)], ['7', '45'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
