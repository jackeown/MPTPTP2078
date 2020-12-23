%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctqTTf1FrS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:17 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 584 expanded)
%              Number of leaves         :   31 ( 189 expanded)
%              Depth                    :   27
%              Number of atoms          : 1303 (5287 expanded)
%              Number of equality atoms :   38 ( 131 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( ( k1_tops_1 @ X19 @ ( k2_struct_0 @ X19 ) )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X18: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ( m2_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('30',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ X0 ) @ X2 ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ X0 )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('80',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('81',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k2_pre_topc @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('92',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( v1_tops_1 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_tops_1 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ( v1_tops_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,
    ( ~ ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('100',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('105',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ X16 )
       != ( k2_struct_0 @ X17 ) )
      | ( v1_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X18: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('116',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('117',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_B @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','123'])).

thf('125',plain,(
    v1_tops_1 @ ( sk_B @ sk_A ) @ sk_A ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['97','125','126'])).

thf('128',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('129',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['27','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctqTTf1FrS
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 627 iterations in 0.206s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(t43_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X19 : $i]:
% 0.46/0.66         (((k1_tops_1 @ X19 @ (k2_struct_0 @ X19)) = (k2_struct_0 @ X19))
% 0.46/0.66          | ~ (l1_pre_topc @ X19)
% 0.46/0.66          | ~ (v2_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.46/0.66  thf(rc4_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ?[B:$i]:
% 0.46/0.66         ( ( v1_tops_1 @ B @ A ) & 
% 0.46/0.66           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B @ X18) @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf(d3_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( v1_tops_1 @ B @ A ) <=>
% 0.46/0.66             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ~ (v1_tops_1 @ X16 @ X17)
% 0.46/0.66          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.66          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X18 : $i]: ((v1_tops_1 @ (sk_B @ X18) @ X18) | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B @ X18) @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf(dt_k2_pre_topc, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( m1_subset_1 @
% 0.46/0.66         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X12)
% 0.46/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.66          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (sk_B @ X0)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf(t35_connsp_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66            ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d2_connsp_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.46/0.66                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.66          | ~ (r1_tarski @ X23 @ (k1_tops_1 @ X24 @ X25))
% 0.46/0.66          | (m2_connsp_2 @ X25 @ X24 @ X23)
% 0.46/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.66          | ~ (l1_pre_topc @ X24)
% 0.46/0.66          | ~ (v2_pre_topc @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.46/0.66          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.46/0.66          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '18'])).
% 0.46/0.66  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1))),
% 0.46/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((~ (r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '23'])).
% 0.46/0.66  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain, (~ (r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.66  thf(dt_k2_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.66  thf('29', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.66  thf('30', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf(t48_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.66          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.46/0.66          | ~ (l1_pre_topc @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.46/0.66             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('35', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf(t1_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.66       ( r1_tarski @ A @ C ) ))).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.46/0.66          | (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '37'])).
% 0.46/0.66  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('41', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X12)
% 0.46/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.66          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.46/0.66             (u1_struct_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.46/0.66             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf(t12_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.46/0.66              (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66              = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf(t7_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.46/0.66           = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      ((((k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['48', '53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         = (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))
% 0.46/0.66         = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['54', '57', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.66              = (u1_struct_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.46/0.66          | (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '68'])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.46/0.66          | (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X2 @ X3)
% 0.46/0.66          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 0.46/0.66      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_xboole_0 @ (u1_struct_0 @ X0) @ X2) @ X1)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (k2_struct_0 @ X0) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['64', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ X0)
% 0.46/0.66          | (r1_tarski @ (k2_struct_0 @ sk_A) @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '72'])).
% 0.46/0.66  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ X0)
% 0.46/0.66          | (r1_tarski @ (k2_struct_0 @ sk_A) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '75'])).
% 0.46/0.66  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('78', plain, ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ (sk_B @ X0)) = (k2_struct_0 @ X0)))),
% 0.46/0.66      inference('clc', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B @ X18) @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.66          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.46/0.66          | ~ (l1_pre_topc @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (sk_B @ X0) @ (k2_pre_topc @ X0 @ (sk_B @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (sk_B @ X0) @ (k2_pre_topc @ X0 @ (sk_B @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['82'])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['79', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0) | (r1_tarski @ (sk_B @ X0) @ (k2_struct_0 @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.66          | ~ (r1_tarski @ X3 @ X4)
% 0.46/0.66          | (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (r1_tarski @ (sk_B @ X0) @ X1)
% 0.46/0.66          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (((r1_tarski @ (sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['78', '87'])).
% 0.46/0.66  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('90', plain, ((r1_tarski @ (sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.66  thf('91', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B @ X18) @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf(t79_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.66                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.66          | ~ (v1_tops_1 @ X20 @ X21)
% 0.46/0.66          | ~ (r1_tarski @ X20 @ X22)
% 0.46/0.66          | (v1_tops_1 @ X22 @ X21)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.66          | ~ (l1_pre_topc @ X21))),
% 0.46/0.66      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | (v1_tops_1 @ X1 @ X0)
% 0.46/0.66          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.46/0.66          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.46/0.66          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.46/0.66          | (v1_tops_1 @ X1 @ X0)
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['94'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.66          | ~ (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 0.46/0.66          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['91', '95'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      ((~ (v1_tops_1 @ (sk_B @ sk_A) @ sk_A)
% 0.46/0.66        | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['90', '96'])).
% 0.46/0.66  thf('98', plain, ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66         = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0) | (r1_tarski @ (sk_B @ X0) @ (k2_struct_0 @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['84'])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_xboole_0 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.46/0.66              = (k2_struct_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '68'])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      (![X9 : $i, X11 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (m1_subset_1 @ X2 @ 
% 0.46/0.66          (k1_zfmisc_1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.66  thf('107', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (sk_B @ X0) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_xboole_0 @ (k2_struct_0 @ X0) @ X1)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['103', '106'])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['100', '107'])).
% 0.46/0.66  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ((k2_pre_topc @ X17 @ X16) != (k2_struct_0 @ X17))
% 0.46/0.66          | (v1_tops_1 @ X16 @ X17)
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v1_tops_1 @ (sk_B @ sk_A) @ sk_A)
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.66  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      (((v1_tops_1 @ (sk_B @ sk_A) @ sk_A)
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (![X18 : $i]: ((v1_tops_1 @ (sk_B @ X18) @ X18) | ~ (l1_pre_topc @ X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('117', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ~ (v1_tops_1 @ X16 @ X17)
% 0.46/0.66          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_tops_1 @ (sk_B @ sk_A) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.66  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      ((((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_tops_1 @ (sk_B @ sk_A) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['115', '120'])).
% 0.46/0.66  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (sk_B @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['121', '122'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (((v1_tops_1 @ (sk_B @ sk_A) @ sk_A)
% 0.46/0.66        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['114', '123'])).
% 0.46/0.66  thf('125', plain, ((v1_tops_1 @ (sk_B @ sk_A) @ sk_A)),
% 0.46/0.66      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.66  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('127', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['97', '125', '126'])).
% 0.46/0.66  thf('128', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('129', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ~ (v1_tops_1 @ X16 @ X17)
% 0.46/0.66          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.46/0.66  thf('130', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.66          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.66  thf('131', plain,
% 0.46/0.66      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['127', '130'])).
% 0.46/0.66  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('133', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['131', '132'])).
% 0.46/0.66  thf('134', plain, ((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['40', '133'])).
% 0.46/0.66  thf('135', plain, ($false), inference('demod', [status(thm)], ['27', '134'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
