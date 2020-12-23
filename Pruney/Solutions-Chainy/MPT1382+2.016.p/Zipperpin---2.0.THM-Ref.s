%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJLzEL4R1k

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 318 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  719 (6611 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t7_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( m1_connsp_2 @ C @ A @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ B )
                            & ( v3_pre_topc @ D @ A )
                            & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_connsp_2 @ X9 @ X8 @ X7 )
      | ( r2_hidden @ X7 @ ( k1_tops_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_tops_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X5 @ ( sk_D @ X3 @ X5 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_B_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_tops_1 @ X4 @ X3 ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( m1_connsp_2 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_tops_1 @ X4 @ X3 ) )
      | ( v3_pre_topc @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    v3_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','39'])).

thf('41',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('45',plain,(
    ! [X13: $i] :
      ( ~ ( r1_tarski @ X13 @ sk_C )
      | ~ ( v3_pre_topc @ X13 @ sk_A )
      | ~ ( m1_connsp_2 @ X13 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['32','38'])).

thf('48',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_tops_1 @ X4 @ X3 ) )
      | ( r1_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    r1_tarski @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47','55'])).

thf('57',plain,(
    r2_hidden @ sk_B_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','59'])).

thf('61',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['43','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJLzEL4R1k
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:29:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 52 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(t7_connsp_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.20/0.49                    ( ![D:$i]:
% 0.20/0.49                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.49                          ( m1_subset_1 @
% 0.20/0.49                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.20/0.49                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.20/0.49                       ( ![D:$i]:
% 0.20/0.49                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.49                             ( m1_subset_1 @
% 0.20/0.49                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.20/0.49                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_connsp_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.49                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (m1_connsp_2 @ X9 @ X8 @ X7)
% 0.20/0.49          | (r2_hidden @ X7 @ (k1_tops_1 @ X8 @ X9))
% 0.20/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.49          | ~ (l1_pre_topc @ X8)
% 0.20/0.49          | ~ (v2_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.49          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.49          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.49  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t54_tops_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i,C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.20/0.49             ( ?[D:$i]:
% 0.20/0.49               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.49                 ( v3_pre_topc @ D @ A ) & 
% 0.20/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (k1_tops_1 @ X4 @ X3))
% 0.20/0.49          | (r2_hidden @ X5 @ (sk_D @ X3 @ X5 @ X4))
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | (r2_hidden @ X0 @ (sk_D @ sk_C @ X0 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (sk_D @ sk_C @ X0 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain, ((r2_hidden @ sk_B_1 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '18'])).
% 0.20/0.49  thf('20', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (k1_tops_1 @ X4 @ X3))
% 0.20/0.49          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.49  thf(t5_connsp_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.49                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.49          | ~ (v3_pre_topc @ X10 @ X11)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.49          | (m1_connsp_2 @ X10 @ X11 @ X12)
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.20/0.49          | ~ (l1_pre_topc @ X11)
% 0.20/0.49          | ~ (v2_pre_topc @ X11)
% 0.20/0.49          | (v2_struct_0 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49          | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (k1_tops_1 @ X4 @ X3))
% 0.20/0.49          | (v3_pre_topc @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | (v3_pre_topc @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v3_pre_topc @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.49  thf('39', plain, ((v3_pre_topc @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '31', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '40'])).
% 0.20/0.49  thf('42', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X13 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X13 @ sk_C)
% 0.20/0.49          | ~ (v3_pre_topc @ X13 @ sk_A)
% 0.20/0.49          | ~ (m1_connsp_2 @ X13 @ sk_A @ sk_B_1)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v1_xboole_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((v1_xboole_0 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.20/0.49        | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r1_tarski @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, ((v3_pre_topc @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '38'])).
% 0.20/0.49  thf('48', plain, ((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (k1_tops_1 @ X4 @ X3))
% 0.20/0.49          | (r1_tarski @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | (r1_tarski @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.49  thf('55', plain, ((r1_tarski @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((v1_xboole_0 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))
% 0.20/0.49        | ~ (m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47', '55'])).
% 0.20/0.49  thf('57', plain, ((r2_hidden @ sk_B_1 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '18'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('59', plain, (~ (v1_xboole_0 @ (sk_D @ sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (~ (m1_connsp_2 @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.20/0.49      inference('clc', [status(thm)], ['56', '59'])).
% 0.20/0.49  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['43', '60'])).
% 0.20/0.49  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
