%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ohwxLDaJIq

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 138 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  607 (1681 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v5_tops_1 @ X11 @ X12 )
      | ( X11
        = ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X7 @ ( k4_subset_1 @ X7 @ X8 @ X6 ) ) @ ( k3_subset_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ ( k2_pre_topc @ X9 @ X10 ) )
        = ( k2_pre_topc @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('36',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','37'])).

thf('39',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','38'])).

thf('40',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','39'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X4 @ X3 ) @ ( k3_subset_1 @ X4 @ X5 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['7','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ohwxLDaJIq
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.19  % Solved by: fo/fo7.sh
% 0.99/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.19  % done 451 iterations in 0.736s
% 0.99/1.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.19  % SZS output start Refutation
% 0.99/1.19  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.19  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.99/1.19  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.19  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.99/1.19  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.99/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.19  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.19  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.19  thf(t103_tops_1, conjecture,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v5_tops_1 @ B @ A ) =>
% 0.99/1.19             ( r1_tarski @
% 0.99/1.19               ( k2_tops_1 @ A @ B ) @ 
% 0.99/1.19               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.19    (~( ![A:$i]:
% 0.99/1.19        ( ( l1_pre_topc @ A ) =>
% 0.99/1.19          ( ![B:$i]:
% 0.99/1.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19              ( ( v5_tops_1 @ B @ A ) =>
% 0.99/1.19                ( r1_tarski @
% 0.99/1.19                  ( k2_tops_1 @ A @ B ) @ 
% 0.99/1.19                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.99/1.19    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.99/1.19  thf('0', plain,
% 0.99/1.19      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('1', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(d7_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v5_tops_1 @ B @ A ) <=>
% 0.99/1.19             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.19  thf('2', plain,
% 0.99/1.19      (![X11 : $i, X12 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.99/1.19          | ~ (v5_tops_1 @ X11 @ X12)
% 0.99/1.19          | ((X11) = (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.99/1.19          | ~ (l1_pre_topc @ X12))),
% 0.99/1.19      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.99/1.19  thf('3', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.19  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('6', plain,
% 0.99/1.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.99/1.19  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.99/1.19      inference('demod', [status(thm)], ['0', '6'])).
% 0.99/1.19  thf('8', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(dt_k2_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.19  thf('9', plain,
% 0.99/1.19      (![X15 : $i, X16 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X15)
% 0.99/1.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.99/1.19          | (m1_subset_1 @ (k2_tops_1 @ X15 @ X16) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.99/1.19  thf('10', plain,
% 0.99/1.19      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.19  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('12', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.19  thf('13', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t41_subset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.19       ( ![C:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.19           ( r1_tarski @
% 0.99/1.19             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.99/1.19             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.99/1.19  thf('14', plain,
% 0.99/1.19      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.99/1.19          | (r1_tarski @ (k3_subset_1 @ X7 @ (k4_subset_1 @ X7 @ X8 @ X6)) @ 
% 0.99/1.19             (k3_subset_1 @ X7 @ X8))
% 0.99/1.19          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t41_subset_1])).
% 0.99/1.19  thf('15', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ 
% 0.99/1.19             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.19              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)) @ 
% 0.99/1.19             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['13', '14'])).
% 0.99/1.19  thf('16', plain,
% 0.99/1.19      ((r1_tarski @ 
% 0.99/1.19        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.19         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)) @ 
% 0.99/1.19        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['12', '15'])).
% 0.99/1.19  thf('17', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.19  thf('18', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(commutativity_k4_subset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.99/1.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.99/1.19       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.99/1.19  thf('19', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.19          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 0.99/1.19          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 0.99/1.19      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.99/1.19  thf('20', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.19            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.19  thf('21', plain,
% 0.99/1.19      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19            sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['17', '20'])).
% 0.99/1.19  thf('22', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t65_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( k2_pre_topc @ A @ B ) =
% 0.99/1.19             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.19  thf('23', plain,
% 0.99/1.19      (![X17 : $i, X18 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.99/1.19          | ((k2_pre_topc @ X18 @ X17)
% 0.99/1.19              = (k4_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 0.99/1.19                 (k2_tops_1 @ X18 @ X17)))
% 0.99/1.19          | ~ (l1_pre_topc @ X18))),
% 0.99/1.19      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.99/1.19  thf('24', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.19            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.19               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.19  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('26', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(dt_k1_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.19  thf('27', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X13)
% 0.99/1.19          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.99/1.19          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.99/1.19  thf('28', plain,
% 0.99/1.19      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['26', '27'])).
% 0.99/1.19  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('30', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['28', '29'])).
% 0.99/1.19  thf(projectivity_k2_pre_topc, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.99/1.19         ( k2_pre_topc @ A @ B ) ) ))).
% 0.99/1.19  thf('31', plain,
% 0.99/1.19      (![X9 : $i, X10 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X9)
% 0.99/1.19          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.99/1.19          | ((k2_pre_topc @ X9 @ (k2_pre_topc @ X9 @ X10))
% 0.99/1.19              = (k2_pre_topc @ X9 @ X10)))),
% 0.99/1.19      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.99/1.19  thf('32', plain,
% 0.99/1.19      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['30', '31'])).
% 0.99/1.19  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('34', plain,
% 0.99/1.19      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['32', '33'])).
% 0.99/1.19  thf('35', plain,
% 0.99/1.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.99/1.19  thf('36', plain,
% 0.99/1.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.99/1.19  thf('37', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.99/1.19  thf('38', plain,
% 0.99/1.19      (((sk_B)
% 0.99/1.19         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.19            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['24', '25', '37'])).
% 0.99/1.19  thf('39', plain,
% 0.99/1.19      (((sk_B)
% 0.99/1.19         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19            sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '38'])).
% 0.99/1.19  thf('40', plain,
% 0.99/1.19      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.99/1.19        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['16', '39'])).
% 0.99/1.19  thf(t31_subset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.19       ( ![C:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.19           ( ( r1_tarski @ B @ C ) <=>
% 0.99/1.19             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.19  thf('41', plain,
% 0.99/1.19      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.99/1.19          | ~ (r1_tarski @ (k3_subset_1 @ X4 @ X3) @ (k3_subset_1 @ X4 @ X5))
% 0.99/1.19          | (r1_tarski @ X5 @ X3)
% 0.99/1.19          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.99/1.19      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.99/1.19  thf('42', plain,
% 0.99/1.19      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.19        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['40', '41'])).
% 0.99/1.19  thf('43', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.19  thf('44', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('45', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.99/1.19      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.99/1.19  thf('46', plain, ($false), inference('demod', [status(thm)], ['7', '45'])).
% 0.99/1.19  
% 0.99/1.19  % SZS output end Refutation
% 0.99/1.19  
% 0.99/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
