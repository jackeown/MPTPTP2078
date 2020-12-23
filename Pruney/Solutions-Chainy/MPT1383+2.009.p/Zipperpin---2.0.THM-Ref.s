%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.izGRRpBrTc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 267 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          : 1446 (5068 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t8_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m1_connsp_2 @ C @ A @ B )
                <=> ? [D: $i] :
                      ( ( r2_hidden @ B @ D )
                      & ( r1_tarski @ D @ C )
                      & ( v3_pre_topc @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_connsp_2])).

thf('0',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( r1_tarski @ X25 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X25 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_connsp_2 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ( r2_hidden @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('66',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('67',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('70',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference(demod,[status(thm)],['67','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,
    ( ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['52'])).

thf('78',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('79',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
   <= ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ sk_D_1 @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('96',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('102',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','76','77','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.izGRRpBrTc
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.63  % Solved by: fo/fo7.sh
% 0.36/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.63  % done 436 iterations in 0.178s
% 0.36/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.63  % SZS output start Refutation
% 0.36/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.63  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.63  thf(t8_connsp_2, conjecture,
% 0.36/0.63    (![A:$i]:
% 0.36/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.63       ( ![B:$i]:
% 0.36/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.63           ( ![C:$i]:
% 0.36/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.63               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.63                 ( ?[D:$i]:
% 0.36/0.63                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.63                     ( v3_pre_topc @ D @ A ) & 
% 0.36/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.63    (~( ![A:$i]:
% 0.36/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.63            ( l1_pre_topc @ A ) ) =>
% 0.36/0.63          ( ![B:$i]:
% 0.36/0.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.63              ( ![C:$i]:
% 0.36/0.63                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.63                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.63                    ( ?[D:$i]:
% 0.36/0.63                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.63                        ( v3_pre_topc @ D @ A ) & 
% 0.36/0.63                        ( m1_subset_1 @
% 0.36/0.63                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.63    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.36/0.63  thf('0', plain,
% 0.36/0.63      (((r1_tarski @ sk_D_1 @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('1', plain,
% 0.36/0.63      (((r1_tarski @ sk_D_1 @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('split', [status(esa)], ['0'])).
% 0.36/0.63  thf('2', plain,
% 0.36/0.63      (((v3_pre_topc @ sk_D_1 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('3', plain,
% 0.36/0.63      (((v3_pre_topc @ sk_D_1 @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('split', [status(esa)], ['2'])).
% 0.36/0.63  thf('4', plain,
% 0.36/0.63      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('5', plain,
% 0.36/0.63      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.36/0.63       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('split', [status(esa)], ['4'])).
% 0.36/0.63  thf('6', plain,
% 0.36/0.63      (![X25 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63          | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.36/0.63          | ~ (r1_tarski @ X25 @ sk_C)
% 0.36/0.63          | ~ (r2_hidden @ sk_B @ X25)
% 0.36/0.63          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('7', plain,
% 0.36/0.63      ((![X25 : $i]:
% 0.36/0.63          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.36/0.63           | ~ (r1_tarski @ X25 @ sk_C)
% 0.36/0.63           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.36/0.63       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.63      inference('split', [status(esa)], ['6'])).
% 0.36/0.63  thf('8', plain,
% 0.36/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(dt_k1_tops_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.63       ( m1_subset_1 @
% 0.36/0.63         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.63  thf('9', plain,
% 0.36/0.63      (![X9 : $i, X10 : $i]:
% 0.36/0.63         (~ (l1_pre_topc @ X9)
% 0.36/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.36/0.63          | (m1_subset_1 @ (k1_tops_1 @ X9 @ X10) @ 
% 0.36/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.36/0.63      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.36/0.63  thf('10', plain,
% 0.36/0.63      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.36/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('12', plain,
% 0.36/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.36/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.63  thf('13', plain,
% 0.36/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(t7_subset_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63       ( ![C:$i]:
% 0.36/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63           ( ( ![D:$i]:
% 0.36/0.63               ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.63                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.36/0.63             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.63  thf('14', plain,
% 0.36/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.63          | (r1_tarski @ X5 @ X3)
% 0.36/0.63          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.36/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.36/0.63  thf('15', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.63             (u1_struct_0 @ sk_A))
% 0.36/0.63          | (r1_tarski @ X0 @ sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.63  thf('16', plain,
% 0.36/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.36/0.63        | (m1_subset_1 @ 
% 0.36/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.63           (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['12', '15'])).
% 0.36/0.63  thf('17', plain,
% 0.36/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.36/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.63  thf('18', plain,
% 0.36/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('19', plain,
% 0.36/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.63          | (r1_tarski @ X5 @ X3)
% 0.36/0.63          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.36/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.36/0.63  thf('20', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.63          | (r2_hidden @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.36/0.63          | (r1_tarski @ X0 @ sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.63  thf('21', plain,
% 0.36/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.36/0.63        | (r2_hidden @ 
% 0.36/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.63           (k1_tops_1 @ sk_A @ sk_C)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.63  thf('22', plain,
% 0.36/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(d1_connsp_2, axiom,
% 0.36/0.63    (![A:$i]:
% 0.36/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.63       ( ![B:$i]:
% 0.36/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.63           ( ![C:$i]:
% 0.36/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.63               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.63                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.63  thf('23', plain,
% 0.36/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.36/0.63          | ~ (r2_hidden @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.36/0.63          | (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.63          | ~ (l1_pre_topc @ X17)
% 0.36/0.63          | ~ (v2_pre_topc @ X17)
% 0.36/0.63          | (v2_struct_0 @ X17))),
% 0.36/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.63  thf('24', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         ((v2_struct_0 @ sk_A)
% 0.36/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.63          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.63  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('27', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         ((v2_struct_0 @ sk_A)
% 0.36/0.63          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | ~ (m1_subset_1 @ 
% 0.47/0.63             (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63             (u1_struct_0 @ sk_A))
% 0.47/0.63        | (m1_connsp_2 @ sk_C @ sk_A @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['21', '27'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (m1_connsp_2 @ sk_C @ sk_A @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['16', '28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (((m1_connsp_2 @ sk_C @ sk_A @ 
% 0.47/0.63         (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.47/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.63  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (m1_connsp_2 @ sk_C @ sk_A @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('clc', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (m1_subset_1 @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63           (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['12', '15'])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t6_connsp_2, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.63               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.47/0.63          | ~ (m1_connsp_2 @ X22 @ X23 @ X24)
% 0.47/0.63          | (r2_hidden @ X24 @ X22)
% 0.47/0.63          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.47/0.63          | ~ (l1_pre_topc @ X23)
% 0.47/0.63          | ~ (v2_pre_topc @ X23)
% 0.47/0.63          | (v2_struct_0 @ X23))),
% 0.47/0.63      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ sk_C)
% 0.47/0.63          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.63  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ sk_C)
% 0.47/0.63          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | ~ (m1_connsp_2 @ sk_C @ sk_A @ 
% 0.47/0.63             (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (r2_hidden @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63           sk_C)
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['33', '39'])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (r2_hidden @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63           sk_C)
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['32', '40'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (((r2_hidden @ 
% 0.47/0.63         (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63         sk_C)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.47/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.63  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (r2_hidden @ 
% 0.47/0.63           (sk_D @ sk_C @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.63           sk_C))),
% 0.47/0.63      inference('clc', [status(thm)], ['42', '43'])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('46', plain,
% 0.47/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.47/0.63          | (r1_tarski @ X5 @ X3)
% 0.47/0.63          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.47/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_C)
% 0.47/0.63          | (r1_tarski @ X0 @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['44', '47'])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.47/0.63      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.63  thf('51', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.47/0.63      inference('simplify', [status(thm)], ['50'])).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ sk_D_1) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('53', plain,
% 0.47/0.63      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.47/0.63         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('split', [status(esa)], ['52'])).
% 0.47/0.63  thf('54', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.47/0.63          | ~ (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.47/0.63          | (r2_hidden @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.63          | ~ (l1_pre_topc @ X17)
% 0.47/0.63          | ~ (v2_pre_topc @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17))),
% 0.47/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.47/0.63  thf('56', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.63  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.47/0.63  thf('60', plain,
% 0.47/0.63      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['53', '59'])).
% 0.47/0.63  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('62', plain,
% 0.47/0.63      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.47/0.63  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('64', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.47/0.63         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['62', '63'])).
% 0.47/0.63  thf('65', plain,
% 0.47/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf('66', plain,
% 0.47/0.63      ((![X25 : $i]:
% 0.47/0.63          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63           | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63           | ~ (r2_hidden @ sk_B @ X25)))
% 0.47/0.63         <= ((![X25 : $i]:
% 0.47/0.63                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.47/0.63      inference('split', [status(esa)], ['6'])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.47/0.63         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.47/0.63         <= ((![X25 : $i]:
% 0.47/0.63                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(fc9_tops_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.47/0.63  thf('69', plain,
% 0.47/0.63      (![X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X11)
% 0.47/0.63          | ~ (v2_pre_topc @ X11)
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.63          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.63  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('73', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.47/0.63      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.47/0.63  thf('74', plain,
% 0.47/0.63      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.47/0.63         <= ((![X25 : $i]:
% 0.47/0.63                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.47/0.63      inference('demod', [status(thm)], ['67', '73'])).
% 0.47/0.63  thf('75', plain,
% 0.47/0.63      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.47/0.63         <= ((![X25 : $i]:
% 0.47/0.63                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63                 | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63                 | ~ (r2_hidden @ sk_B @ X25))) & 
% 0.47/0.63             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['64', '74'])).
% 0.47/0.63  thf('76', plain,
% 0.47/0.63      (~
% 0.47/0.63       (![X25 : $i]:
% 0.47/0.63          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.47/0.63           | ~ (r1_tarski @ X25 @ sk_C)
% 0.47/0.63           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.47/0.63       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.47/0.63      inference('sup-', [status(thm)], ['51', '75'])).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ sk_D_1)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.47/0.63      inference('split', [status(esa)], ['52'])).
% 0.47/0.63  thf('78', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ sk_D_1)) <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.47/0.63      inference('split', [status(esa)], ['52'])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      (((r1_tarski @ sk_D_1 @ sk_C)) <= (((r1_tarski @ sk_D_1 @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('80', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      (((v3_pre_topc @ sk_D_1 @ sk_A)) <= (((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.47/0.63      inference('split', [status(esa)], ['2'])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('split', [status(esa)], ['4'])).
% 0.47/0.63  thf(t56_tops_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf('83', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | ~ (v3_pre_topc @ X13 @ X14)
% 0.47/0.63          | ~ (r1_tarski @ X13 @ X15)
% 0.47/0.63          | (r1_tarski @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | ~ (l1_pre_topc @ X14))),
% 0.47/0.63      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.47/0.63  thf('84', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (l1_pre_topc @ sk_A)
% 0.47/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.47/0.63           | ~ (r1_tarski @ sk_D_1 @ X0)
% 0.47/0.63           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)))
% 0.47/0.63         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.63  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.47/0.63           | ~ (r1_tarski @ sk_D_1 @ X0)
% 0.47/0.63           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)))
% 0.47/0.63         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.63  thf('87', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          (~ (r1_tarski @ sk_D_1 @ X0)
% 0.47/0.63           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.47/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.63         <= (((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['81', '86'])).
% 0.47/0.63  thf('88', plain,
% 0.47/0.63      ((((r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63         | ~ (r1_tarski @ sk_D_1 @ sk_C)))
% 0.47/0.63         <= (((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['80', '87'])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      (((r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.47/0.63         <= (((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['79', '88'])).
% 0.47/0.63  thf(t3_subset, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.63  thf('90', plain,
% 0.47/0.63      (![X6 : $i, X8 : $i]:
% 0.47/0.63         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.47/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.63  thf('91', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.47/0.63         <= (((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.63  thf(l3_subset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.47/0.63  thf('92', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.63          | (r2_hidden @ X0 @ X2)
% 0.47/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.47/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.47/0.63  thf('93', plain,
% 0.47/0.63      ((![X0 : $i]:
% 0.47/0.63          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63           | ~ (r2_hidden @ X0 @ sk_D_1)))
% 0.47/0.63         <= (((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.47/0.63  thf('94', plain,
% 0.47/0.63      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.47/0.63         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.47/0.63             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['78', '93'])).
% 0.47/0.63  thf('95', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ sk_A)
% 0.47/0.63          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.63  thf('96', plain,
% 0.47/0.63      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.47/0.63             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['94', '95'])).
% 0.47/0.63  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('98', plain,
% 0.47/0.63      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.47/0.63             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.63  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('100', plain,
% 0.47/0.63      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.47/0.63         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.47/0.63             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.47/0.63             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.47/0.63             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('clc', [status(thm)], ['98', '99'])).
% 0.47/0.63  thf('101', plain,
% 0.47/0.63      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.47/0.63         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.63      inference('split', [status(esa)], ['6'])).
% 0.47/0.63  thf('102', plain,
% 0.47/0.63      (~ ((r2_hidden @ sk_B @ sk_D_1)) | 
% 0.47/0.63       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.47/0.63       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.47/0.63       ~ ((v3_pre_topc @ sk_D_1 @ sk_A)) | ~ ((r1_tarski @ sk_D_1 @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.63  thf('103', plain, ($false),
% 0.47/0.63      inference('sat_resolution*', [status(thm)],
% 0.47/0.63                ['1', '3', '5', '7', '76', '77', '102'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
