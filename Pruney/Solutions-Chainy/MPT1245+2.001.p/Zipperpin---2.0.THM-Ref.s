%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VBlphUMkbF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 789 expanded)
%              Number of leaves         :   34 ( 252 expanded)
%              Depth                    :   15
%              Number of atoms          : 1047 (8868 expanded)
%              Number of equality atoms :   75 ( 626 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t59_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              = ( k2_pre_topc @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
                = ( k2_pre_topc @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_pre_topc @ X31 @ ( k1_tops_1 @ X31 @ X30 ) )
        = ( k2_pre_topc @ X31 @ ( k1_tops_1 @ X31 @ ( k2_pre_topc @ X31 @ ( k1_tops_1 @ X31 @ X30 ) ) ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t58_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('15',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('32',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['32','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('49',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

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

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('71',plain,
    ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('76',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','50','71','77','78'])).

thf('80',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','50','71','77','78'])).

thf('81',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','79','80'])).

thf('82',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
 != ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VBlphUMkbF
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 235 iterations in 0.128s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(t59_tops_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v3_pre_topc @ B @ A ) =>
% 0.37/0.58             ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.37/0.58               ( k2_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( l1_pre_topc @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58              ( ( v3_pre_topc @ B @ A ) =>
% 0.37/0.58                ( ( k2_pre_topc @
% 0.37/0.58                    A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.37/0.58                  ( k2_pre_topc @ A @ B ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t59_tops_1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t58_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.37/0.58             ( k2_pre_topc @
% 0.37/0.58               A @ 
% 0.37/0.58               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X30 : $i, X31 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.37/0.58          | ((k2_pre_topc @ X31 @ (k1_tops_1 @ X31 @ X30))
% 0.37/0.58              = (k2_pre_topc @ X31 @ 
% 0.37/0.58                 (k1_tops_1 @ X31 @ 
% 0.37/0.58                  (k2_pre_topc @ X31 @ (k1_tops_1 @ X31 @ X30)))))
% 0.37/0.58          | ~ (l1_pre_topc @ X31))),
% 0.37/0.58      inference('cnf', [status(esa)], [t58_tops_1])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.58            = (k2_pre_topc @ sk_A @ 
% 0.37/0.58               (k1_tops_1 @ sk_A @ 
% 0.37/0.58                (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.58         = (k2_pre_topc @ sk_A @ 
% 0.37/0.58            (k1_tops_1 @ sk_A @ 
% 0.37/0.58             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.58  thf(d4_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.37/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.37/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.37/0.58          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.37/0.58          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('eq_fact', [status(thm)], ['5'])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(l3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X16 @ X17)
% 0.37/0.58          | (r2_hidden @ X16 @ X18)
% 0.37/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((sk_B) = (k3_xboole_0 @ sk_B @ X0))
% 0.37/0.58          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.37/0.58         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.37/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.37/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.37/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      ((((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.58        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.58        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.58        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      ((~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.58        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.37/0.58          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('eq_fact', [status(thm)], ['5'])).
% 0.37/0.58  thf('15', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf(commutativity_k2_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.58  thf(t12_setfam_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf(t48_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.58           = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.58           = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.58           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.58           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['20', '23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['15', '24'])).
% 0.37/0.58  thf('26', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.37/0.58           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.37/0.58  thf(t36_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.37/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.58  thf(t3_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X21 : $i, X23 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf(d1_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.58             ( k3_subset_1 @
% 0.37/0.58               ( u1_struct_0 @ A ) @ 
% 0.37/0.58               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X26 : $i, X27 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.58          | ((k1_tops_1 @ X27 @ X26)
% 0.37/0.58              = (k3_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.37/0.58                 (k2_pre_topc @ X27 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26))))
% 0.37/0.58          | ~ (l1_pre_topc @ X27))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.37/0.58              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.37/0.58                 (k2_pre_topc @ X0 @ 
% 0.37/0.58                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.37/0.58                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf(d5_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.37/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.58           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.58           = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.58           = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.37/0.58              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.37/0.58                 (k2_pre_topc @ X0 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.37/0.58      inference('demod', [status(thm)], ['37', '42'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_A @ 
% 0.37/0.58          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.58          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58             (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup+', [status(thm)], ['32', '43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.37/0.58           = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('49', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.37/0.58  thf('51', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf(t29_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.58             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X28 : $i, X29 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.58          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.37/0.58          | (v4_pre_topc @ X28 @ X29)
% 0.37/0.58          | ~ (l1_pre_topc @ X29))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.37/0.58          | ~ (v3_pre_topc @ 
% 0.37/0.58               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.37/0.58                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.37/0.58               X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.58           = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.37/0.58          | ~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.58  thf('58', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v3_pre_topc @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.37/0.58          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.37/0.58          | ~ (l1_pre_topc @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['52', '57'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['51', '58'])).
% 0.37/0.58  thf('60', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('62', plain,
% 0.37/0.58      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf(t52_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('64', plain,
% 0.37/0.58      (![X24 : $i, X25 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.58          | ~ (v4_pre_topc @ X24 @ X25)
% 0.37/0.58          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.37/0.58          | ~ (l1_pre_topc @ X25))),
% 0.37/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.58  thf('65', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X0)
% 0.37/0.58          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.37/0.58              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.37/0.58          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.58  thf('66', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['62', '65'])).
% 0.37/0.58  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('68', plain,
% 0.37/0.58      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.58  thf('69', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('70', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('71', plain,
% 0.37/0.58      (((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.37/0.58  thf('72', plain,
% 0.37/0.58      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.37/0.58         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('73', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.58           = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('74', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.58         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['72', '73'])).
% 0.37/0.58  thf('75', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('76', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('77', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.37/0.58  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('79', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['44', '50', '71', '77', '78'])).
% 0.37/0.58  thf('80', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['44', '50', '71', '77', '78'])).
% 0.37/0.58  thf('81', plain,
% 0.37/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.58         = (k2_pre_topc @ sk_A @ 
% 0.37/0.58            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.37/0.58      inference('demod', [status(thm)], ['4', '79', '80'])).
% 0.37/0.58  thf('82', plain,
% 0.37/0.58      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.37/0.58         != (k2_pre_topc @ sk_A @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('83', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
