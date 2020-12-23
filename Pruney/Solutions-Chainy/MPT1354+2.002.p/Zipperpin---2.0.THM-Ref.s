%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLn5eKNiDG

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 197 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  728 (2457 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t79_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tops_2 @ B @ A )
            <=> ( r1_tarski @ B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tops_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t52_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( r1_tarski @ X6 @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('15',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( r1_tarski @ X10 @ ( u1_pre_topc @ X11 ) )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t17_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t17_tops_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('27',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ~ ( v2_tops_2 @ sk_B @ sk_A )
   <= ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ X4 )
      | ( r1_tarski @ X6 @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_tarski @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_tops_2 @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( u1_pre_topc @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t17_tops_2])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('51',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','31','52'])).

thf('54',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['48','49','50','54'])).

thf('56',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['33','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLn5eKNiDG
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 97 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.52  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(t79_tops_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.52             ( r1_tarski @
% 0.20/0.52               B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_pre_topc @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @
% 0.20/0.52                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52              ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.52                ( r1_tarski @
% 0.20/0.52                  B @ 
% 0.20/0.52                  ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t79_tops_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.52        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tarski @ sk_B @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.52       ~ ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.52        | (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_u1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( u1_pre_topc @ A ) @ 
% 0.20/0.52         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X7 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.52          | ~ (l1_pre_topc @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf(t52_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.20/0.52             ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.20/0.52          | ~ (r1_tarski @ X6 @ (k7_setfam_1 @ X5 @ X4))
% 0.20/0.52          | (r1_tarski @ (k7_setfam_1 @ X5 @ X6) @ X4)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.52          | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.20/0.52             (u1_pre_topc @ X0))
% 0.20/0.52          | ~ (r1_tarski @ X1 @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.52        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.52        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52         (u1_pre_topc @ sk_A)))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k7_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf(t78_tops_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.52          | ~ (r1_tarski @ X10 @ (u1_pre_topc @ X11))
% 0.20/0.52          | (v1_tops_2 @ X10 @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.52        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52             (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.52        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52             (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf(t17_tops_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.52             ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_tops_2 @ X8 @ X9)
% 0.20/0.52          | (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_tops_2])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v2_tops_2 @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.52           sk_A)
% 0.20/0.52        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.52        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((v2_tops_2 @ sk_B @ sk_A))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ 
% 0.20/0.52               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (v2_tops_2 @ sk_B @ sk_A)) <= (~ ((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v2_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.52       ~
% 0.20/0.52       ((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (~ (r1_tarski @ sk_B @ 
% 0.20/0.52          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X7 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.52          | ~ (l1_pre_topc @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.20/0.52          | ~ (r1_tarski @ (k7_setfam_1 @ X5 @ X6) @ X4)
% 0.20/0.52          | (r1_tarski @ X6 @ (k7_setfam_1 @ X5 @ X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.52          | (r1_tarski @ X1 @ 
% 0.20/0.52             (k7_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.20/0.52               (u1_pre_topc @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A))
% 0.20/0.52        | (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.52  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A))
% 0.20/0.52        | (r1_tarski @ sk_B @ 
% 0.20/0.52           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.52          | ~ (v1_tops_2 @ X10 @ X11)
% 0.20/0.52          | (r1_tarski @ X10 @ (u1_pre_topc @ X11))
% 0.20/0.52          | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A))
% 0.20/0.52        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52         (u1_pre_topc @ sk_A))
% 0.20/0.52        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.20/0.52          | (v1_tops_2 @ X8 @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_tops_2])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.52        | ~ (v2_tops_2 @ 
% 0.20/0.52             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.52             sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v2_tops_2 @ sk_B @ sk_A)) <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((v2_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.52       ((r1_tarski @ sk_B @ 
% 0.20/0.52         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('53', plain, (((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '31', '52'])).
% 0.20/0.52  thf('54', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['48', '49', '50', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.52        (u1_pre_topc @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((r1_tarski @ sk_B @ 
% 0.20/0.52        (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '56'])).
% 0.20/0.52  thf('58', plain, ($false), inference('demod', [status(thm)], ['33', '57'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
