%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RlSpfYpCCq

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  506 (1325 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(t22_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r2_waybel_7 @ A @ B @ D ) )
         => ( r2_waybel_7 @ A @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ B @ C )
              & ( r2_waybel_7 @ A @ B @ D ) )
           => ( r2_waybel_7 @ A @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_yellow19])).

thf('0',plain,(
    ~ ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_waybel_7 @ sk_A @ sk_B @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r2_waybel_7 @ A @ B @ C )
        <=> ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ C @ D ) )
               => ( r2_hidden @ D @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ X0 @ X1 @ X2 ) )
      | ( r2_waybel_7 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ X1 @ X2 ) @ X2 )
      | ( r2_waybel_7 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r2_waybel_7 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_waybel_7 @ X2 @ X1 @ X3 )
      | ~ ( v3_pre_topc @ X4 @ X2 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X4 )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_waybel_7 @ X0 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_waybel_7 @ X0 @ X3 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 )
      | ( v1_xboole_0 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X1 )
      | ( r2_waybel_7 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 )
    | ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r2_waybel_7 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ sk_C ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_waybel_7 @ sk_A @ X0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).


%------------------------------------------------------------------------------
