%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C9YljwsB3a

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:49 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  641 (1513 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v5_tops_1 @ X14 @ X15 )
      | ( X14
        = ( k2_pre_topc @ X15 @ ( k1_tops_1 @ X15 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ X7 ) @ ( k3_subset_1 @ X6 @ ( k9_subset_1 @ X6 @ X7 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_tops_1 @ X13 @ X12 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ X12 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_pre_topc @ X10 @ ( k2_pre_topc @ X10 @ X11 ) )
        = ( k2_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('34',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('35',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','35'])).

thf('37',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','36'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ( r1_tarski @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['39','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['7','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C9YljwsB3a
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.67/1.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.67/1.91  % Solved by: fo/fo7.sh
% 1.67/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.67/1.91  % done 1020 iterations in 1.460s
% 1.67/1.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.67/1.91  % SZS output start Refutation
% 1.67/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.67/1.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.67/1.91  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.67/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.67/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.67/1.91  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.67/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.67/1.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.67/1.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.67/1.91  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.67/1.91  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.67/1.91  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.67/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.67/1.91  thf(t103_tops_1, conjecture,
% 1.67/1.91    (![A:$i]:
% 1.67/1.91     ( ( l1_pre_topc @ A ) =>
% 1.67/1.91       ( ![B:$i]:
% 1.67/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.91           ( ( v5_tops_1 @ B @ A ) =>
% 1.67/1.91             ( r1_tarski @
% 1.67/1.91               ( k2_tops_1 @ A @ B ) @ 
% 1.67/1.91               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.67/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.67/1.91    (~( ![A:$i]:
% 1.67/1.91        ( ( l1_pre_topc @ A ) =>
% 1.67/1.91          ( ![B:$i]:
% 1.67/1.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.91              ( ( v5_tops_1 @ B @ A ) =>
% 1.67/1.91                ( r1_tarski @
% 1.67/1.91                  ( k2_tops_1 @ A @ B ) @ 
% 1.67/1.91                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.67/1.91    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.67/1.91  thf('0', plain,
% 1.67/1.91      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.91          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf('1', plain,
% 1.67/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf(d7_tops_1, axiom,
% 1.67/1.91    (![A:$i]:
% 1.67/1.91     ( ( l1_pre_topc @ A ) =>
% 1.67/1.91       ( ![B:$i]:
% 1.67/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.91           ( ( v5_tops_1 @ B @ A ) <=>
% 1.67/1.91             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.67/1.91  thf('2', plain,
% 1.67/1.91      (![X14 : $i, X15 : $i]:
% 1.67/1.91         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.67/1.91          | ~ (v5_tops_1 @ X14 @ X15)
% 1.67/1.91          | ((X14) = (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 1.67/1.91          | ~ (l1_pre_topc @ X15))),
% 1.67/1.91      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.67/1.91  thf('3', plain,
% 1.67/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.67/1.91        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.67/1.91        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.67/1.91      inference('sup-', [status(thm)], ['1', '2'])).
% 1.67/1.91  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf('6', plain,
% 1.67/1.91      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.91      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.67/1.91  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.67/1.91      inference('demod', [status(thm)], ['0', '6'])).
% 1.67/1.91  thf('8', plain,
% 1.67/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf('9', plain,
% 1.67/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf(dt_k3_subset_1, axiom,
% 1.67/1.91    (![A:$i,B:$i]:
% 1.67/1.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.67/1.91       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.67/1.91  thf('10', plain,
% 1.67/1.91      (![X0 : $i, X1 : $i]:
% 1.67/1.91         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.67/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.67/1.91      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.67/1.91  thf('11', plain,
% 1.67/1.91      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.67/1.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.91      inference('sup-', [status(thm)], ['9', '10'])).
% 1.67/1.91  thf(dt_k2_pre_topc, axiom,
% 1.67/1.91    (![A:$i,B:$i]:
% 1.67/1.91     ( ( ( l1_pre_topc @ A ) & 
% 1.67/1.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.67/1.91       ( m1_subset_1 @
% 1.67/1.91         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.67/1.91  thf('12', plain,
% 1.67/1.91      (![X8 : $i, X9 : $i]:
% 1.67/1.91         (~ (l1_pre_topc @ X8)
% 1.67/1.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.67/1.91          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 1.67/1.91             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 1.67/1.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.67/1.91  thf('13', plain,
% 1.67/1.91      (((m1_subset_1 @ 
% 1.67/1.91         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.67/1.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.67/1.91        | ~ (l1_pre_topc @ sk_A))),
% 1.67/1.91      inference('sup-', [status(thm)], ['11', '12'])).
% 1.67/1.91  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.91  thf('15', plain,
% 1.67/1.91      ((m1_subset_1 @ 
% 1.67/1.91        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.67/1.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.91      inference('demod', [status(thm)], ['13', '14'])).
% 1.67/1.91  thf(t42_subset_1, axiom,
% 1.67/1.91    (![A:$i,B:$i]:
% 1.67/1.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.67/1.91       ( ![C:$i]:
% 1.67/1.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.67/1.91           ( r1_tarski @
% 1.67/1.91             ( k3_subset_1 @ A @ B ) @ 
% 1.67/1.91             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.67/1.91  thf('16', plain,
% 1.67/1.91      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.67/1.91         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.67/1.91          | (r1_tarski @ (k3_subset_1 @ X6 @ X7) @ 
% 1.67/1.91             (k3_subset_1 @ X6 @ (k9_subset_1 @ X6 @ X7 @ X5)))
% 1.67/1.91          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.67/1.91      inference('cnf', [status(esa)], [t42_subset_1])).
% 1.67/1.91  thf('17', plain,
% 1.67/1.91      (![X0 : $i]:
% 1.67/1.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.67/1.91          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.67/1.91             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.67/1.91              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.67/1.91               (k2_pre_topc @ sk_A @ 
% 1.67/1.91                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.67/1.92  thf('18', plain,
% 1.67/1.92      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.67/1.92        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.67/1.92         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.67/1.92          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['8', '17'])).
% 1.67/1.92  thf('19', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(d2_tops_1, axiom,
% 1.67/1.92    (![A:$i]:
% 1.67/1.92     ( ( l1_pre_topc @ A ) =>
% 1.67/1.92       ( ![B:$i]:
% 1.67/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.92           ( ( k2_tops_1 @ A @ B ) =
% 1.67/1.92             ( k9_subset_1 @
% 1.67/1.92               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.67/1.92               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.67/1.92  thf('20', plain,
% 1.67/1.92      (![X12 : $i, X13 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.67/1.92          | ((k2_tops_1 @ X13 @ X12)
% 1.67/1.92              = (k9_subset_1 @ (u1_struct_0 @ X13) @ 
% 1.67/1.92                 (k2_pre_topc @ X13 @ X12) @ 
% 1.67/1.92                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 1.67/1.92          | ~ (l1_pre_topc @ X13))),
% 1.67/1.92      inference('cnf', [status(esa)], [d2_tops_1])).
% 1.67/1.92  thf('21', plain,
% 1.67/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.67/1.92        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.67/1.92            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.67/1.92               (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.67/1.92               (k2_pre_topc @ sk_A @ 
% 1.67/1.92                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['19', '20'])).
% 1.67/1.92  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('23', plain,
% 1.67/1.92      (((k2_tops_1 @ sk_A @ sk_B)
% 1.67/1.92         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.67/1.92            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.67/1.92      inference('demod', [status(thm)], ['21', '22'])).
% 1.67/1.92  thf('24', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(dt_k1_tops_1, axiom,
% 1.67/1.92    (![A:$i,B:$i]:
% 1.67/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.67/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.67/1.92       ( m1_subset_1 @
% 1.67/1.92         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.67/1.92  thf('25', plain,
% 1.67/1.92      (![X16 : $i, X17 : $i]:
% 1.67/1.92         (~ (l1_pre_topc @ X16)
% 1.67/1.92          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.67/1.92          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 1.67/1.92             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.67/1.92  thf('26', plain,
% 1.67/1.92      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.92         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.67/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.67/1.92      inference('sup-', [status(thm)], ['24', '25'])).
% 1.67/1.92  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('28', plain,
% 1.67/1.92      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('demod', [status(thm)], ['26', '27'])).
% 1.67/1.92  thf(projectivity_k2_pre_topc, axiom,
% 1.67/1.92    (![A:$i,B:$i]:
% 1.67/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.67/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.67/1.92       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 1.67/1.92         ( k2_pre_topc @ A @ B ) ) ))).
% 1.67/1.92  thf('29', plain,
% 1.67/1.92      (![X10 : $i, X11 : $i]:
% 1.67/1.92         (~ (l1_pre_topc @ X10)
% 1.67/1.92          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.67/1.92          | ((k2_pre_topc @ X10 @ (k2_pre_topc @ X10 @ X11))
% 1.67/1.92              = (k2_pre_topc @ X10 @ X11)))),
% 1.67/1.92      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 1.67/1.92  thf('30', plain,
% 1.67/1.92      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.67/1.92          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.67/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.67/1.92      inference('sup-', [status(thm)], ['28', '29'])).
% 1.67/1.92  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('32', plain,
% 1.67/1.92      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.67/1.92         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['30', '31'])).
% 1.67/1.92  thf('33', plain,
% 1.67/1.92      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.67/1.92  thf('34', plain,
% 1.67/1.92      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.67/1.92  thf('35', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.67/1.92      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.67/1.92  thf('36', plain,
% 1.67/1.92      (((k2_tops_1 @ sk_A @ sk_B)
% 1.67/1.92         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.67/1.92            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.67/1.92      inference('demod', [status(thm)], ['23', '35'])).
% 1.67/1.92  thf('37', plain,
% 1.67/1.92      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.67/1.92        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.67/1.92      inference('demod', [status(thm)], ['18', '36'])).
% 1.67/1.92  thf(t31_subset_1, axiom,
% 1.67/1.92    (![A:$i,B:$i]:
% 1.67/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.67/1.92       ( ![C:$i]:
% 1.67/1.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.67/1.92           ( ( r1_tarski @ B @ C ) <=>
% 1.67/1.92             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.67/1.92  thf('38', plain,
% 1.67/1.92      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.67/1.92         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.67/1.92          | ~ (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 1.67/1.92          | (r1_tarski @ X4 @ X2)
% 1.67/1.92          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 1.67/1.92      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.67/1.92  thf('39', plain,
% 1.67/1.92      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.92           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.67/1.92        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.67/1.92        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.67/1.92      inference('sup-', [status(thm)], ['37', '38'])).
% 1.67/1.92  thf('40', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf(dt_k2_tops_1, axiom,
% 1.67/1.92    (![A:$i,B:$i]:
% 1.67/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.67/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.67/1.92       ( m1_subset_1 @
% 1.67/1.92         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.67/1.92  thf('41', plain,
% 1.67/1.92      (![X18 : $i, X19 : $i]:
% 1.67/1.92         (~ (l1_pre_topc @ X18)
% 1.67/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.67/1.92          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 1.67/1.92             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.67/1.92      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.67/1.92  thf('42', plain,
% 1.67/1.92      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.92         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.67/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.67/1.92      inference('sup-', [status(thm)], ['40', '41'])).
% 1.67/1.92  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('44', plain,
% 1.67/1.92      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.67/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('demod', [status(thm)], ['42', '43'])).
% 1.67/1.92  thf('45', plain,
% 1.67/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.67/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.92  thf('46', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.67/1.92      inference('demod', [status(thm)], ['39', '44', '45'])).
% 1.67/1.92  thf('47', plain, ($false), inference('demod', [status(thm)], ['7', '46'])).
% 1.67/1.92  
% 1.67/1.92  % SZS output end Refutation
% 1.67/1.92  
% 1.75/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
