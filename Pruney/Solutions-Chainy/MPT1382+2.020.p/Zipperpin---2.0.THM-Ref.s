%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8iiNxAvka

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:52 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 329 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  784 (6685 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X12 @ ( sk_D @ X10 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X11 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X17 )
      | ( m1_connsp_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X11 @ X10 ) )
      | ( v3_pre_topc @ ( sk_D @ X10 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','39'])).

thf('41',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ X20 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( m1_connsp_2 @ X20 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['32','38'])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X11 @ X10 ) )
      | ( r1_tarski @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','55'])).

thf('57',plain,(
    r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    ~ ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','66'])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['43','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8iiNxAvka
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 173 iterations in 0.134s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.59  thf(t7_connsp_2, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.38/0.59                    ( ![D:$i]:
% 0.38/0.59                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.38/0.59                          ( m1_subset_1 @
% 0.38/0.59                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.59                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.38/0.59                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59            ( l1_pre_topc @ A ) ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59              ( ![C:$i]:
% 0.38/0.59                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.38/0.59                       ( ![D:$i]:
% 0.38/0.59                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.38/0.59                             ( m1_subset_1 @
% 0.38/0.59                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.59                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.38/0.59                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.38/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d1_connsp_2, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.38/0.59                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.38/0.59          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.38/0.59          | (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.38/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.59          | ~ (l1_pre_topc @ X15)
% 0.38/0.59          | ~ (v2_pre_topc @ X15)
% 0.38/0.59          | (v2_struct_0 @ X15))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.38/0.59          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.38/0.59          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '7'])).
% 0.38/0.59  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.38/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t54_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i,C:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.38/0.59             ( ?[D:$i]:
% 0.38/0.59               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.38/0.59                 ( v3_pre_topc @ D @ A ) & 
% 0.38/0.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X11 @ X10))
% 0.38/0.59          | (r2_hidden @ X12 @ (sk_D @ X10 @ X12 @ X11))
% 0.38/0.59          | ~ (l1_pre_topc @ X11)
% 0.38/0.59          | ~ (v2_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ X0 @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.59  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r2_hidden @ X0 @ (sk_D @ sk_C_1 @ X0 @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.38/0.59  thf('19', plain, ((r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['12', '18'])).
% 0.38/0.59  thf('20', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.38/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X11 @ X10))
% 0.38/0.59          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | ~ (l1_pre_topc @ X11)
% 0.38/0.59          | ~ (v2_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.59  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['20', '26'])).
% 0.38/0.59  thf(t5_connsp_2, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.38/0.59                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.59          | ~ (v3_pre_topc @ X17 @ X18)
% 0.38/0.59          | ~ (r2_hidden @ X19 @ X17)
% 0.38/0.59          | (m1_connsp_2 @ X17 @ X18 @ X19)
% 0.38/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.38/0.59          | ~ (l1_pre_topc @ X18)
% 0.38/0.59          | ~ (v2_pre_topc @ X18)
% 0.38/0.59          | (v2_struct_0 @ X18))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.38/0.59          | ~ (v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.38/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X11 @ X10))
% 0.38/0.59          | (v3_pre_topc @ (sk_D @ X10 @ X12 @ X11) @ X11)
% 0.38/0.59          | ~ (l1_pre_topc @ X11)
% 0.38/0.59          | ~ (v2_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (v3_pre_topc @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v3_pre_topc @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.59  thf('39', plain, ((v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['29', '30', '31', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (((m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.38/0.59        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['19', '40'])).
% 0.38/0.59  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (((m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['20', '26'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X20 : $i]:
% 0.38/0.59         (~ (r1_tarski @ X20 @ sk_C_1)
% 0.38/0.59          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.38/0.59          | ~ (m1_connsp_2 @ X20 @ sk_A @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.59          | (v1_xboole_0 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (((v1_xboole_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.38/0.59        | ~ (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.38/0.59        | ~ (v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.59  thf('47', plain, ((v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '38'])).
% 0.38/0.59  thf('48', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.38/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.59          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X11 @ X10))
% 0.38/0.59          | (r1_tarski @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 0.38/0.59          | ~ (l1_pre_topc @ X11)
% 0.38/0.59          | ~ (v2_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.59  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.38/0.59  thf('55', plain, ((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)),
% 0.38/0.59      inference('sup-', [status(thm)], ['48', '54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (((v1_xboole_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.38/0.59        | ~ (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['46', '47', '55'])).
% 0.38/0.59  thf('57', plain, ((r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['12', '18'])).
% 0.38/0.59  thf(d3_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.59  thf('61', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.59      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.59  thf(t3_subset, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (![X4 : $i, X6 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.59  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.59  thf(t5_subset, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.59          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X7 @ X8)
% 0.38/0.59          | ~ (v1_xboole_0 @ X9)
% 0.38/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.59  thf('66', plain, (~ (v1_xboole_0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['57', '65'])).
% 0.38/0.59  thf('67', plain,
% 0.38/0.59      (~ (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.38/0.59      inference('clc', [status(thm)], ['56', '66'])).
% 0.38/0.59  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('clc', [status(thm)], ['43', '67'])).
% 0.38/0.59  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
