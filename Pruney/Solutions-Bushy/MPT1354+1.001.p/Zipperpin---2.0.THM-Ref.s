%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1354+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t20uU6cAzA

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:33 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 383 expanded)
%              Number of leaves         :   26 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          : 1480 (5021 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( v2_tops_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( v2_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( X9
       != ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( v2_tops_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( v2_tops_2 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( v2_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('35',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( v2_tops_2 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v2_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v2_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('42',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( v2_tops_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['39','50'])).

thf('52',plain,
    ( ~ ( v2_tops_2 @ sk_B @ sk_A )
   <= ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('66',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v2_tops_2 @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( v4_pre_topc @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v4_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('84',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['64','85'])).

thf('87',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( X9
       != ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ( r2_hidden @ X12 @ ( k7_setfam_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['55','101'])).


%------------------------------------------------------------------------------
