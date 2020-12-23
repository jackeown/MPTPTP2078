%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CN3c9UspQY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:49 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 141 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  705 (1738 expanded)
%              Number of equality atoms :   20 (  26 expanded)
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

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v5_tops_1 @ X16 @ X17 )
      | ( X16
        = ( k2_pre_topc @ X17 @ ( k1_tops_1 @ X17 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_tops_1 @ X15 @ X14 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ X14 ) @ ( k2_pre_topc @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_pre_topc @ X10 @ ( k2_pre_topc @ X10 @ X11 ) )
        = ( k2_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('34',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('38',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','39'])).

thf('41',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','40'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ( r1_tarski @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['43','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['7','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CN3c9UspQY
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:02:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.48/1.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.48/1.66  % Solved by: fo/fo7.sh
% 1.48/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.48/1.66  % done 944 iterations in 1.216s
% 1.48/1.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.48/1.66  % SZS output start Refutation
% 1.48/1.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.48/1.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.48/1.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.48/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.48/1.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.48/1.66  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.48/1.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.48/1.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.48/1.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.48/1.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.48/1.66  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.48/1.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.48/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.48/1.66  thf(t103_tops_1, conjecture,
% 1.48/1.66    (![A:$i]:
% 1.48/1.66     ( ( l1_pre_topc @ A ) =>
% 1.48/1.66       ( ![B:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.48/1.66           ( ( v5_tops_1 @ B @ A ) =>
% 1.48/1.66             ( r1_tarski @
% 1.48/1.66               ( k2_tops_1 @ A @ B ) @ 
% 1.48/1.66               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.48/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.48/1.66    (~( ![A:$i]:
% 1.48/1.66        ( ( l1_pre_topc @ A ) =>
% 1.48/1.66          ( ![B:$i]:
% 1.48/1.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.48/1.66              ( ( v5_tops_1 @ B @ A ) =>
% 1.48/1.66                ( r1_tarski @
% 1.48/1.66                  ( k2_tops_1 @ A @ B ) @ 
% 1.48/1.66                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.48/1.66    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.48/1.66  thf('0', plain,
% 1.48/1.66      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.48/1.66          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('1', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf(d7_tops_1, axiom,
% 1.48/1.66    (![A:$i]:
% 1.48/1.66     ( ( l1_pre_topc @ A ) =>
% 1.48/1.66       ( ![B:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.48/1.66           ( ( v5_tops_1 @ B @ A ) <=>
% 1.48/1.66             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.48/1.66  thf('2', plain,
% 1.48/1.66      (![X16 : $i, X17 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.48/1.66          | ~ (v5_tops_1 @ X16 @ X17)
% 1.48/1.66          | ((X16) = (k2_pre_topc @ X17 @ (k1_tops_1 @ X17 @ X16)))
% 1.48/1.66          | ~ (l1_pre_topc @ X17))),
% 1.48/1.66      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.48/1.66  thf('3', plain,
% 1.48/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.48/1.66        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.48/1.66        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.48/1.66      inference('sup-', [status(thm)], ['1', '2'])).
% 1.48/1.66  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('6', plain,
% 1.48/1.66      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.48/1.66  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.48/1.66      inference('demod', [status(thm)], ['0', '6'])).
% 1.48/1.66  thf('8', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('9', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf(dt_k3_subset_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.48/1.66       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.48/1.66  thf('10', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.48/1.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.48/1.66      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.48/1.66  thf('11', plain,
% 1.48/1.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('sup-', [status(thm)], ['9', '10'])).
% 1.48/1.66  thf(dt_k2_pre_topc, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( ( l1_pre_topc @ A ) & 
% 1.48/1.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.48/1.66       ( m1_subset_1 @
% 1.48/1.66         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.48/1.66  thf('12', plain,
% 1.48/1.66      (![X8 : $i, X9 : $i]:
% 1.48/1.66         (~ (l1_pre_topc @ X8)
% 1.48/1.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.48/1.66          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 1.48/1.66             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 1.48/1.66      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.48/1.66  thf('13', plain,
% 1.48/1.66      (((m1_subset_1 @ 
% 1.48/1.66         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.48/1.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.48/1.66        | ~ (l1_pre_topc @ sk_A))),
% 1.48/1.66      inference('sup-', [status(thm)], ['11', '12'])).
% 1.48/1.66  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('15', plain,
% 1.48/1.66      ((m1_subset_1 @ 
% 1.48/1.66        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('demod', [status(thm)], ['13', '14'])).
% 1.48/1.66  thf(t42_subset_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.48/1.66       ( ![C:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.48/1.66           ( r1_tarski @
% 1.48/1.66             ( k3_subset_1 @ A @ B ) @ 
% 1.48/1.66             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.48/1.66  thf('16', plain,
% 1.48/1.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.48/1.66          | (r1_tarski @ (k3_subset_1 @ X6 @ X7) @ 
% 1.48/1.66             (k3_subset_1 @ X6 @ (k9_subset_1 @ X6 @ X7 @ X5)))
% 1.48/1.66          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.48/1.66      inference('cnf', [status(esa)], [t42_subset_1])).
% 1.48/1.66  thf('17', plain,
% 1.48/1.66      (![X0 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.48/1.66          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.48/1.66             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.48/1.66               (k2_pre_topc @ sk_A @ 
% 1.48/1.66                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['15', '16'])).
% 1.48/1.66  thf('18', plain,
% 1.48/1.66      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.48/1.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.48/1.66          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['8', '17'])).
% 1.48/1.66  thf('19', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf(d2_tops_1, axiom,
% 1.48/1.66    (![A:$i]:
% 1.48/1.66     ( ( l1_pre_topc @ A ) =>
% 1.48/1.66       ( ![B:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.48/1.66           ( ( k2_tops_1 @ A @ B ) =
% 1.48/1.66             ( k9_subset_1 @
% 1.48/1.66               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.48/1.66               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.48/1.66  thf('20', plain,
% 1.48/1.66      (![X14 : $i, X15 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.48/1.66          | ((k2_tops_1 @ X15 @ X14)
% 1.48/1.66              = (k9_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.48/1.66                 (k2_pre_topc @ X15 @ X14) @ 
% 1.48/1.66                 (k2_pre_topc @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14))))
% 1.48/1.66          | ~ (l1_pre_topc @ X15))),
% 1.48/1.66      inference('cnf', [status(esa)], [d2_tops_1])).
% 1.48/1.66  thf('21', plain,
% 1.48/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.48/1.66        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.48/1.66            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66               (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.48/1.66               (k2_pre_topc @ sk_A @ 
% 1.48/1.66                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['19', '20'])).
% 1.48/1.66  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('23', plain,
% 1.48/1.66      (((k2_tops_1 @ sk_A @ sk_B)
% 1.48/1.66         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.48/1.66            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.48/1.66      inference('demod', [status(thm)], ['21', '22'])).
% 1.48/1.66  thf('24', plain,
% 1.48/1.66      ((m1_subset_1 @ 
% 1.48/1.66        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('demod', [status(thm)], ['13', '14'])).
% 1.48/1.66  thf('25', plain,
% 1.48/1.66      (![X0 : $i, X1 : $i]:
% 1.48/1.66         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.48/1.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.48/1.66      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.48/1.66  thf('26', plain,
% 1.48/1.66      ((m1_subset_1 @ 
% 1.48/1.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('sup-', [status(thm)], ['24', '25'])).
% 1.48/1.66  thf('27', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf(d1_tops_1, axiom,
% 1.48/1.66    (![A:$i]:
% 1.48/1.66     ( ( l1_pre_topc @ A ) =>
% 1.48/1.66       ( ![B:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.48/1.66           ( ( k1_tops_1 @ A @ B ) =
% 1.48/1.66             ( k3_subset_1 @
% 1.48/1.66               ( u1_struct_0 @ A ) @ 
% 1.48/1.66               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.48/1.66  thf('28', plain,
% 1.48/1.66      (![X12 : $i, X13 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.48/1.66          | ((k1_tops_1 @ X13 @ X12)
% 1.48/1.66              = (k3_subset_1 @ (u1_struct_0 @ X13) @ 
% 1.48/1.66                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 1.48/1.66          | ~ (l1_pre_topc @ X13))),
% 1.48/1.66      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.48/1.66  thf('29', plain,
% 1.48/1.66      ((~ (l1_pre_topc @ sk_A)
% 1.48/1.66        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.48/1.66            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66               (k2_pre_topc @ sk_A @ 
% 1.48/1.66                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['27', '28'])).
% 1.48/1.66  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('31', plain,
% 1.48/1.66      (((k1_tops_1 @ sk_A @ sk_B)
% 1.48/1.66         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.48/1.66            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.48/1.66      inference('demod', [status(thm)], ['29', '30'])).
% 1.48/1.66  thf('32', plain,
% 1.48/1.66      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('demod', [status(thm)], ['26', '31'])).
% 1.48/1.66  thf(projectivity_k2_pre_topc, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( ( l1_pre_topc @ A ) & 
% 1.48/1.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.48/1.66       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 1.48/1.66         ( k2_pre_topc @ A @ B ) ) ))).
% 1.48/1.66  thf('33', plain,
% 1.48/1.66      (![X10 : $i, X11 : $i]:
% 1.48/1.66         (~ (l1_pre_topc @ X10)
% 1.48/1.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.48/1.66          | ((k2_pre_topc @ X10 @ (k2_pre_topc @ X10 @ X11))
% 1.48/1.66              = (k2_pre_topc @ X10 @ X11)))),
% 1.48/1.66      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 1.48/1.66  thf('34', plain,
% 1.48/1.66      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.48/1.66          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.48/1.66        | ~ (l1_pre_topc @ sk_A))),
% 1.48/1.66      inference('sup-', [status(thm)], ['32', '33'])).
% 1.48/1.66  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('36', plain,
% 1.48/1.66      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.48/1.66         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('demod', [status(thm)], ['34', '35'])).
% 1.48/1.66  thf('37', plain,
% 1.48/1.66      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.48/1.66  thf('38', plain,
% 1.48/1.66      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.48/1.66  thf('39', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.48/1.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.48/1.66  thf('40', plain,
% 1.48/1.66      (((k2_tops_1 @ sk_A @ sk_B)
% 1.48/1.66         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.48/1.66            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.48/1.66      inference('demod', [status(thm)], ['23', '39'])).
% 1.48/1.66  thf('41', plain,
% 1.48/1.66      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.48/1.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.48/1.66      inference('demod', [status(thm)], ['18', '40'])).
% 1.48/1.66  thf(t31_subset_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.48/1.66       ( ![C:$i]:
% 1.48/1.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.48/1.66           ( ( r1_tarski @ B @ C ) <=>
% 1.48/1.66             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.48/1.66  thf('42', plain,
% 1.48/1.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.48/1.66         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.48/1.66          | ~ (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 1.48/1.66          | (r1_tarski @ X4 @ X2)
% 1.48/1.66          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 1.48/1.66      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.48/1.66  thf('43', plain,
% 1.48/1.66      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.48/1.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.48/1.66        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.48/1.66        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.48/1.66      inference('sup-', [status(thm)], ['41', '42'])).
% 1.48/1.66  thf('44', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf(dt_k2_tops_1, axiom,
% 1.48/1.66    (![A:$i,B:$i]:
% 1.48/1.66     ( ( ( l1_pre_topc @ A ) & 
% 1.48/1.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.48/1.66       ( m1_subset_1 @
% 1.48/1.66         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.48/1.66  thf('45', plain,
% 1.48/1.66      (![X18 : $i, X19 : $i]:
% 1.48/1.66         (~ (l1_pre_topc @ X18)
% 1.48/1.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.48/1.66          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 1.48/1.66             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.48/1.66      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.48/1.66  thf('46', plain,
% 1.48/1.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.48/1.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.48/1.66        | ~ (l1_pre_topc @ sk_A))),
% 1.48/1.66      inference('sup-', [status(thm)], ['44', '45'])).
% 1.48/1.66  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('48', plain,
% 1.48/1.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.48/1.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('demod', [status(thm)], ['46', '47'])).
% 1.48/1.66  thf('49', plain,
% 1.48/1.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.48/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.48/1.66  thf('50', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.48/1.66      inference('demod', [status(thm)], ['43', '48', '49'])).
% 1.48/1.66  thf('51', plain, ($false), inference('demod', [status(thm)], ['7', '50'])).
% 1.48/1.66  
% 1.48/1.66  % SZS output end Refutation
% 1.48/1.66  
% 1.48/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
