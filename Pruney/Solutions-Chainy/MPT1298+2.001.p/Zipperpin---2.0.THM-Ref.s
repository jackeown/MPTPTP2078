%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OCuFNNBKTO

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 434 expanded)
%              Number of leaves         :   24 ( 129 expanded)
%              Depth                    :   18
%              Number of atoms          : 1237 (5566 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t16_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tops_2 @ B @ A )
            <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tops_2])).

thf('0',plain,
    ( ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X20 ) @ X19 )
      | ( v2_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ ( k3_subset_1 @ X7 @ X6 ) @ ( k7_setfam_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('20',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( v2_tops_2 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('35',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ X19 @ X20 ) @ X20 )
      | ( v2_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['30','43'])).

thf('45',plain,
    ( ~ ( v2_tops_2 @ sk_B @ sk_A )
   <= ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('48',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('55',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) @ X15 )
      | ( v3_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('57',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('67',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( X0
       != ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v2_tops_2 @ X19 @ X20 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ( v4_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('81',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('82',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','46','81'])).

thf('83',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('89',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['65','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['48','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OCuFNNBKTO
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 139 iterations in 0.111s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.57  thf(t16_tops_2, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @
% 0.20/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.57             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( l1_pre_topc @ A ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( m1_subset_1 @
% 0.20/0.57                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57              ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.57                ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t16_tops_2])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.57         <= (~
% 0.20/0.57             ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (~ ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.57       ~ ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d2_tops_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @
% 0.20/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.57             ( ![C:$i]:
% 0.20/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.57          | (r2_hidden @ (sk_C_1 @ X19 @ X20) @ X19)
% 0.20/0.57          | (v2_tops_2 @ X19 @ X20)
% 0.20/0.57          | ~ (l1_pre_topc @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t49_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.57          | ~ (r2_hidden @ X6 @ X8)
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ X7 @ X6) @ (k7_setfam_1 @ X7 @ X8))
% 0.20/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t4_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.57          | (m1_subset_1 @ X9 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['10', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.57         <= (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_k7_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( m1_subset_1 @
% 0.20/0.57         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.20/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf(d1_tops_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @
% 0.20/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.57             ( ![C:$i]:
% 0.20/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X16 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.20/0.57          | ~ (v1_tops_2 @ X16 @ X17)
% 0.20/0.57          | ~ (r2_hidden @ X18 @ X16)
% 0.20/0.57          | (v3_pre_topc @ X18 @ X17)
% 0.20/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.57          | ~ (l1_pre_topc @ X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          (~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.57         <= (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.57          | (m1_subset_1 @ X9 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((v3_pre_topc @ X0 @ sk_A)
% 0.20/0.57           | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.57         <= (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('clc', [status(thm)], ['25', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      ((((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57         | (v3_pre_topc @ 
% 0.20/0.57            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.57            sk_A)))
% 0.20/0.57         <= (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf(t29_tops_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.57             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.57          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.20/0.57          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.57          | ~ (l1_pre_topc @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v4_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.57        | ~ (v3_pre_topc @ 
% 0.20/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | (v4_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.57        | ~ (v3_pre_topc @ 
% 0.20/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.57          | ~ (v4_pre_topc @ (sk_C_1 @ X19 @ X20) @ X20)
% 0.20/0.57          | (v2_tops_2 @ X19 @ X20)
% 0.20/0.57          | ~ (l1_pre_topc @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | ~ (v4_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.57        | ~ (v4_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      ((~ (v3_pre_topc @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 0.20/0.57        | (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('clc', [status(thm)], ['37', '42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A))
% 0.20/0.57         <= (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('clc', [status(thm)], ['30', '43'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((~ (v2_tops_2 @ sk_B @ sk_A)) <= (~ ((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.57       ~ ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (~ ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X16 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.20/0.57          | (r2_hidden @ (sk_C @ X16 @ X17) @ X16)
% 0.20/0.57          | (v1_tops_2 @ X16 @ X17)
% 0.20/0.57          | ~ (l1_pre_topc @ X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.57  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (m1_subset_1 @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.57  thf(t30_tops_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.57             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.57          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14) @ X15)
% 0.20/0.57          | (v3_pre_topc @ X14 @ X15)
% 0.20/0.57          | ~ (l1_pre_topc @ X15))),
% 0.20/0.57      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v3_pre_topc @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.57        | ~ (v4_pre_topc @ 
% 0.20/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57              (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (v3_pre_topc @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.57        | ~ (v4_pre_topc @ 
% 0.20/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57              (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (![X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X16 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.20/0.57          | ~ (v3_pre_topc @ (sk_C @ X16 @ X17) @ X17)
% 0.20/0.57          | (v1_tops_2 @ X16 @ X17)
% 0.20/0.57          | ~ (l1_pre_topc @ X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v3_pre_topc @ 
% 0.20/0.57             (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v3_pre_topc @ 
% 0.20/0.57             (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      ((~ (v4_pre_topc @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57           sk_A)
% 0.20/0.57        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('clc', [status(thm)], ['59', '64'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf(d8_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57             ( ![D:$i]:
% 0.20/0.57               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.57          | ((X0) != (k7_setfam_1 @ X1 @ X2))
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.20/0.57          | ~ (r2_hidden @ X3 @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.20/0.57          | ~ (r2_hidden @ X3 @ (k7_setfam_1 @ X1 @ X2))
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.20/0.57          | ~ (m1_subset_1 @ (k7_setfam_1 @ X1 @ X2) @ 
% 0.20/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (m1_subset_1 @ sk_B @ 
% 0.20/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['67', '69'])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B))),
% 0.20/0.57      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['66', '74'])).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X19 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.20/0.57          | ~ (v2_tops_2 @ X19 @ X20)
% 0.20/0.57          | ~ (r2_hidden @ X21 @ X19)
% 0.20/0.57          | (v4_pre_topc @ X21 @ X20)
% 0.20/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.57          | ~ (l1_pre_topc @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.57          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.57  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('80', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)) <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['16'])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      (((v2_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.57       ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('split', [status(esa)], ['16'])).
% 0.20/0.57  thf('82', plain, (((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '46', '81'])).
% 0.20/0.57  thf('83', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['78', '79', '83'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.57      inference('clc', [status(thm)], ['84', '85'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (v4_pre_topc @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57           sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['75', '86'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      (~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      ((v4_pre_topc @ 
% 0.20/0.57        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57         (sk_C @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) @ 
% 0.20/0.57        sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.57      inference('demod', [status(thm)], ['65', '89'])).
% 0.20/0.57  thf('91', plain, ($false), inference('demod', [status(thm)], ['48', '90'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
