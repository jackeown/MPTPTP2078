%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SB79ajKhP6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:46 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 200 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  836 (2467 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X8 @ X7 ) @ ( k3_subset_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v5_tops_1 @ X15 @ X16 )
      | ( X15
        = ( k2_pre_topc @ X16 @ ( k1_tops_1 @ X16 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['16','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ ( k4_subset_1 @ X11 @ X12 @ X10 ) ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k4_subset_1 @ X5 @ X4 @ X6 )
        = ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_pre_topc @ X13 @ ( k2_pre_topc @ X13 @ X14 ) )
        = ( k2_pre_topc @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('47',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('51',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k4_subset_1 @ X5 @ X4 @ X6 )
        = ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','52','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['35','36','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('62',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['25','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SB79ajKhP6
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:41:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.26/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.26/1.47  % Solved by: fo/fo7.sh
% 1.26/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.26/1.47  % done 697 iterations in 1.002s
% 1.26/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.26/1.47  % SZS output start Refutation
% 1.26/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.26/1.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.26/1.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.26/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.26/1.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.26/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.26/1.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.26/1.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.26/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.26/1.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.26/1.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.26/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.26/1.47  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.26/1.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.26/1.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.26/1.47  thf(t103_tops_1, conjecture,
% 1.26/1.47    (![A:$i]:
% 1.26/1.47     ( ( l1_pre_topc @ A ) =>
% 1.26/1.47       ( ![B:$i]:
% 1.26/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.26/1.47           ( ( v5_tops_1 @ B @ A ) =>
% 1.26/1.47             ( r1_tarski @
% 1.26/1.47               ( k2_tops_1 @ A @ B ) @ 
% 1.26/1.47               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.26/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.26/1.47    (~( ![A:$i]:
% 1.26/1.47        ( ( l1_pre_topc @ A ) =>
% 1.26/1.47          ( ![B:$i]:
% 1.26/1.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.26/1.47              ( ( v5_tops_1 @ B @ A ) =>
% 1.26/1.47                ( r1_tarski @
% 1.26/1.47                  ( k2_tops_1 @ A @ B ) @ 
% 1.26/1.47                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.26/1.47    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.26/1.47  thf('0', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(d5_subset_1, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.26/1.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.26/1.47  thf('1', plain,
% 1.26/1.47      (![X2 : $i, X3 : $i]:
% 1.26/1.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 1.26/1.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.26/1.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.26/1.47  thf('2', plain,
% 1.26/1.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.26/1.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.26/1.47      inference('sup-', [status(thm)], ['0', '1'])).
% 1.26/1.47  thf('3', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(dt_k2_tops_1, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( ( l1_pre_topc @ A ) & 
% 1.26/1.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.26/1.47       ( m1_subset_1 @
% 1.26/1.47         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.26/1.47  thf('4', plain,
% 1.26/1.47      (![X19 : $i, X20 : $i]:
% 1.26/1.47         (~ (l1_pre_topc @ X19)
% 1.26/1.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.26/1.47          | (m1_subset_1 @ (k2_tops_1 @ X19 @ X20) @ 
% 1.26/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.26/1.47      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.26/1.47  thf('5', plain,
% 1.26/1.47      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.26/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.26/1.47      inference('sup-', [status(thm)], ['3', '4'])).
% 1.26/1.47  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('7', plain,
% 1.26/1.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.26/1.47  thf('8', plain,
% 1.26/1.47      (![X2 : $i, X3 : $i]:
% 1.26/1.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 1.26/1.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.26/1.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.26/1.47  thf('9', plain,
% 1.26/1.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.26/1.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('sup-', [status(thm)], ['7', '8'])).
% 1.26/1.47  thf(t31_subset_1, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.26/1.47       ( ![C:$i]:
% 1.26/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.26/1.47           ( ( r1_tarski @ B @ C ) <=>
% 1.26/1.47             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.26/1.47  thf('10', plain,
% 1.26/1.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.26/1.47          | ~ (r1_tarski @ (k3_subset_1 @ X8 @ X7) @ (k3_subset_1 @ X8 @ X9))
% 1.26/1.47          | (r1_tarski @ X9 @ X7)
% 1.26/1.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.26/1.47      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.26/1.47  thf('11', plain,
% 1.26/1.47      (![X0 : $i]:
% 1.26/1.47         (~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.26/1.47             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47          | ~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.26/1.47          | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.26/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.26/1.47      inference('sup-', [status(thm)], ['9', '10'])).
% 1.26/1.47  thf('12', plain,
% 1.26/1.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.26/1.47  thf('13', plain,
% 1.26/1.47      (![X0 : $i]:
% 1.26/1.47         (~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.26/1.47             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47          | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.26/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.26/1.47      inference('demod', [status(thm)], ['11', '12'])).
% 1.26/1.47  thf('14', plain,
% 1.26/1.47      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.26/1.47           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.26/1.47        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.26/1.47      inference('sup-', [status(thm)], ['2', '13'])).
% 1.26/1.47  thf('15', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('16', plain,
% 1.26/1.47      ((~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.26/1.47           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.26/1.47      inference('demod', [status(thm)], ['14', '15'])).
% 1.26/1.47  thf('17', plain,
% 1.26/1.47      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('18', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(d7_tops_1, axiom,
% 1.26/1.47    (![A:$i]:
% 1.26/1.47     ( ( l1_pre_topc @ A ) =>
% 1.26/1.47       ( ![B:$i]:
% 1.26/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.26/1.47           ( ( v5_tops_1 @ B @ A ) <=>
% 1.26/1.47             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.26/1.47  thf('19', plain,
% 1.26/1.47      (![X15 : $i, X16 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.26/1.47          | ~ (v5_tops_1 @ X15 @ X16)
% 1.26/1.47          | ((X15) = (k2_pre_topc @ X16 @ (k1_tops_1 @ X16 @ X15)))
% 1.26/1.47          | ~ (l1_pre_topc @ X16))),
% 1.26/1.47      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.26/1.47  thf('20', plain,
% 1.26/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.26/1.47        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.26/1.47      inference('sup-', [status(thm)], ['18', '19'])).
% 1.26/1.47  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('22', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('23', plain,
% 1.26/1.47      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.26/1.47  thf('24', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.26/1.47      inference('demod', [status(thm)], ['17', '23'])).
% 1.26/1.47  thf('25', plain,
% 1.26/1.47      (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.26/1.47          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('clc', [status(thm)], ['16', '24'])).
% 1.26/1.47  thf('26', plain,
% 1.26/1.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.26/1.47  thf('27', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(t41_subset_1, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.26/1.47       ( ![C:$i]:
% 1.26/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.26/1.47           ( r1_tarski @
% 1.26/1.47             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.26/1.47             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.26/1.47  thf('28', plain,
% 1.26/1.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.26/1.47          | (r1_tarski @ 
% 1.26/1.47             (k3_subset_1 @ X11 @ (k4_subset_1 @ X11 @ X12 @ X10)) @ 
% 1.26/1.47             (k3_subset_1 @ X11 @ X12))
% 1.26/1.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.26/1.47      inference('cnf', [status(esa)], [t41_subset_1])).
% 1.26/1.47  thf('29', plain,
% 1.26/1.47      (![X0 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.26/1.47          | (r1_tarski @ 
% 1.26/1.47             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.26/1.47              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)) @ 
% 1.26/1.47             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.26/1.47      inference('sup-', [status(thm)], ['27', '28'])).
% 1.26/1.47  thf('30', plain,
% 1.26/1.47      ((r1_tarski @ 
% 1.26/1.47        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.26/1.47         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)) @ 
% 1.26/1.47        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('sup-', [status(thm)], ['26', '29'])).
% 1.26/1.47  thf('31', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('32', plain,
% 1.26/1.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.26/1.47  thf(redefinition_k4_subset_1, axiom,
% 1.26/1.47    (![A:$i,B:$i,C:$i]:
% 1.26/1.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.26/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.26/1.47       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.26/1.47  thf('33', plain,
% 1.26/1.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.26/1.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 1.26/1.47          | ((k4_subset_1 @ X5 @ X4 @ X6) = (k2_xboole_0 @ X4 @ X6)))),
% 1.26/1.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.26/1.47  thf('34', plain,
% 1.26/1.47      (![X0 : $i]:
% 1.26/1.47         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.26/1.47            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.26/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.26/1.47      inference('sup-', [status(thm)], ['32', '33'])).
% 1.26/1.47  thf('35', plain,
% 1.26/1.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.26/1.47         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.26/1.47      inference('sup-', [status(thm)], ['31', '34'])).
% 1.26/1.47  thf(commutativity_k2_xboole_0, axiom,
% 1.26/1.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.26/1.47  thf('36', plain,
% 1.26/1.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.26/1.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.26/1.47  thf('37', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(t65_tops_1, axiom,
% 1.26/1.47    (![A:$i]:
% 1.26/1.47     ( ( l1_pre_topc @ A ) =>
% 1.26/1.47       ( ![B:$i]:
% 1.26/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.26/1.47           ( ( k2_pre_topc @ A @ B ) =
% 1.26/1.47             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.26/1.47  thf('38', plain,
% 1.26/1.47      (![X21 : $i, X22 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.26/1.47          | ((k2_pre_topc @ X22 @ X21)
% 1.26/1.47              = (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 1.26/1.47                 (k2_tops_1 @ X22 @ X21)))
% 1.26/1.47          | ~ (l1_pre_topc @ X22))),
% 1.26/1.47      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.26/1.47  thf('39', plain,
% 1.26/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.26/1.47        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.26/1.47            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.26/1.47               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.26/1.47      inference('sup-', [status(thm)], ['37', '38'])).
% 1.26/1.47  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('41', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf(dt_k1_tops_1, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( ( l1_pre_topc @ A ) & 
% 1.26/1.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.26/1.47       ( m1_subset_1 @
% 1.26/1.47         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.26/1.47  thf('42', plain,
% 1.26/1.47      (![X17 : $i, X18 : $i]:
% 1.26/1.47         (~ (l1_pre_topc @ X17)
% 1.26/1.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.26/1.47          | (m1_subset_1 @ (k1_tops_1 @ X17 @ X18) @ 
% 1.26/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 1.26/1.47      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.26/1.47  thf('43', plain,
% 1.26/1.47      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.26/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.26/1.47      inference('sup-', [status(thm)], ['41', '42'])).
% 1.26/1.47  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('45', plain,
% 1.26/1.47      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['43', '44'])).
% 1.26/1.47  thf(projectivity_k2_pre_topc, axiom,
% 1.26/1.47    (![A:$i,B:$i]:
% 1.26/1.47     ( ( ( l1_pre_topc @ A ) & 
% 1.26/1.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.26/1.47       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 1.26/1.47         ( k2_pre_topc @ A @ B ) ) ))).
% 1.26/1.47  thf('46', plain,
% 1.26/1.47      (![X13 : $i, X14 : $i]:
% 1.26/1.47         (~ (l1_pre_topc @ X13)
% 1.26/1.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.26/1.47          | ((k2_pre_topc @ X13 @ (k2_pre_topc @ X13 @ X14))
% 1.26/1.47              = (k2_pre_topc @ X13 @ X14)))),
% 1.26/1.47      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 1.26/1.47  thf('47', plain,
% 1.26/1.47      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.26/1.47      inference('sup-', [status(thm)], ['45', '46'])).
% 1.26/1.47  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('49', plain,
% 1.26/1.47      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.26/1.47         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['47', '48'])).
% 1.26/1.47  thf('50', plain,
% 1.26/1.47      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.26/1.47  thf('51', plain,
% 1.26/1.47      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.26/1.47  thf('52', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.26/1.47      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.26/1.47  thf('53', plain,
% 1.26/1.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.26/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.26/1.47  thf('54', plain,
% 1.26/1.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.26/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.47  thf('55', plain,
% 1.26/1.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.26/1.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 1.26/1.47          | ((k4_subset_1 @ X5 @ X4 @ X6) = (k2_xboole_0 @ X4 @ X6)))),
% 1.26/1.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.26/1.47  thf('56', plain,
% 1.26/1.47      (![X0 : $i]:
% 1.26/1.47         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.26/1.47            = (k2_xboole_0 @ sk_B @ X0))
% 1.26/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.26/1.47      inference('sup-', [status(thm)], ['54', '55'])).
% 1.26/1.47  thf('57', plain,
% 1.26/1.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.26/1.47         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('sup-', [status(thm)], ['53', '56'])).
% 1.26/1.47  thf('58', plain,
% 1.26/1.47      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['39', '40', '52', '57'])).
% 1.26/1.47  thf('59', plain,
% 1.26/1.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.26/1.47         = (sk_B))),
% 1.26/1.47      inference('demod', [status(thm)], ['35', '36', '58'])).
% 1.26/1.47  thf('60', plain,
% 1.26/1.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.26/1.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.26/1.47      inference('sup-', [status(thm)], ['0', '1'])).
% 1.26/1.47  thf('61', plain,
% 1.26/1.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.26/1.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('sup-', [status(thm)], ['7', '8'])).
% 1.26/1.47  thf('62', plain,
% 1.26/1.47      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.26/1.47        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.26/1.47      inference('demod', [status(thm)], ['30', '59', '60', '61'])).
% 1.26/1.47  thf('63', plain, ($false), inference('demod', [status(thm)], ['25', '62'])).
% 1.26/1.47  
% 1.26/1.47  % SZS output end Refutation
% 1.26/1.47  
% 1.35/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
