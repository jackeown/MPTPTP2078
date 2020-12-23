%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t6l3W52sVG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 263 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          : 1052 (5239 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
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
    ! [X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X7 @ sk_A )
      | ~ ( r1_tarski @ X7 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X7 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X7: $i] :
        ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X7 @ sk_A )
        | ~ ( r1_tarski @ X7 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X7 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ ( k1_tops_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ! [X7: $i] :
        ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X7 @ sk_A )
        | ~ ( r1_tarski @ X7 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X7 ) )
   <= ! [X7: $i] :
        ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X7 @ sk_A )
        | ~ ( r1_tarski @ X7 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X7 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('28',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ! [X7: $i] :
          ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X7 @ sk_A )
          | ~ ( r1_tarski @ X7 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X7 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( sk_D @ X0 @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( ~ ! [X7: $i] :
          ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X7 @ sk_A )
          | ~ ( r1_tarski @ X7 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X7 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','36','44','52'])).

thf('54',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('58',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
   <= ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X0 )
      | ~ ( v3_pre_topc @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ~ ( r1_tarski @ sk_D_1 @ sk_C )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_tops_1 @ X5 @ X6 ) )
      | ( m1_connsp_2 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('82',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D_1 @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','53','55','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t6l3W52sVG
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 61 iterations in 0.034s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.52  thf(t8_connsp_2, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.52                 ( ?[D:$i]:
% 0.19/0.52                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.19/0.52                     ( v3_pre_topc @ D @ A ) & 
% 0.19/0.52                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.52            ( l1_pre_topc @ A ) ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52              ( ![C:$i]:
% 0.19/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.52                    ( ?[D:$i]:
% 0.19/0.52                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.19/0.52                        ( v3_pre_topc @ D @ A ) & 
% 0.19/0.52                        ( m1_subset_1 @
% 0.19/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ sk_D_1) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ sk_D_1)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (((r1_tarski @ sk_D_1 @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (((r1_tarski @ sk_D_1 @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.19/0.52       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('split', [status(esa)], ['4'])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X7 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52          | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52          | ~ (r2_hidden @ sk_B @ X7)
% 0.19/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((![X7 : $i]:
% 0.19/0.52          (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52           | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52           | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52           | ~ (r2_hidden @ sk_B @ X7))) | 
% 0.19/0.52       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('split', [status(esa)], ['6'])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_connsp_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.19/0.52          | ~ (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.19/0.52          | (r2_hidden @ X4 @ (k1_tops_1 @ X5 @ X6))
% 0.19/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.52          | ~ (l1_pre_topc @ X5)
% 0.19/0.52          | ~ (v2_pre_topc @ X5)
% 0.19/0.52          | (v2_struct_0 @ X5))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.52  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.52         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['8', '14'])).
% 0.19/0.52  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.52  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t54_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i,C:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.19/0.52             ( ?[D:$i]:
% 0.19/0.52               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.19/0.52                 ( v3_pre_topc @ D @ A ) & 
% 0.19/0.52                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 0.19/0.52          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | ~ (v2_pre_topc @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.52  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ 
% 0.19/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['19', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      ((![X7 : $i]:
% 0.19/0.52          (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52           | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52           | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52           | ~ (r2_hidden @ sk_B @ X7)))
% 0.19/0.52         <= ((![X7 : $i]:
% 0.19/0.52                (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52                 | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52                 | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52                 | ~ (r2_hidden @ sk_B @ X7))))),
% 0.19/0.52      inference('split', [status(esa)], ['6'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (((~ (r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.19/0.52         | ~ (r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.52         | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.19/0.52         <= ((![X7 : $i]:
% 0.19/0.52                (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52                 | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52                 | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52                 | ~ (r2_hidden @ sk_B @ X7))) & 
% 0.19/0.52             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 0.19/0.52          | (r2_hidden @ X2 @ (sk_D @ X0 @ X2 @ X1))
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | ~ (v2_pre_topc @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (sk_D @ sk_C @ X0 @ sk_A))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ X0 @ (sk_D @ sk_C @ X0 @ sk_A))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['29', '35'])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 0.19/0.52          | (r1_tarski @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | ~ (v2_pre_topc @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (r1_tarski @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r1_tarski @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      (((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['37', '43'])).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 0.19/0.52          | (v3_pre_topc @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | ~ (v2_pre_topc @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (v3_pre_topc @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.52  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v3_pre_topc @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.52      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.19/0.52  thf('52', plain,
% 0.19/0.52      (((v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))
% 0.19/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['45', '51'])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      (~
% 0.19/0.52       (![X7 : $i]:
% 0.19/0.52          (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52           | ~ (v3_pre_topc @ X7 @ sk_A)
% 0.19/0.52           | ~ (r1_tarski @ X7 @ sk_C)
% 0.19/0.52           | ~ (r2_hidden @ sk_B @ X7))) | 
% 0.19/0.52       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['28', '36', '44', '52'])).
% 0.19/0.52  thf('54', plain,
% 0.19/0.52      (((v3_pre_topc @ sk_D_1 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('55', plain,
% 0.19/0.52      (((v3_pre_topc @ sk_D_1 @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('split', [status(esa)], ['54'])).
% 0.19/0.52  thf('56', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ sk_D_1)) <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('57', plain,
% 0.19/0.52      (((v3_pre_topc @ sk_D_1 @ sk_A)) <= (((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['54'])).
% 0.19/0.52  thf('58', plain,
% 0.19/0.52      (((r1_tarski @ sk_D_1 @ sk_C)) <= (((r1_tarski @ sk_D_1 @ sk_C)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('59', plain,
% 0.19/0.52      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.19/0.52         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('split', [status(esa)], ['4'])).
% 0.19/0.52  thf('60', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('61', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.52          | ~ (r1_tarski @ X3 @ X0)
% 0.19/0.52          | ~ (v3_pre_topc @ X3 @ X1)
% 0.19/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.52          | (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | ~ (v2_pre_topc @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.19/0.52  thf('62', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ sk_C)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.52  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('65', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ sk_C)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.52      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.19/0.52  thf('66', plain,
% 0.19/0.52      ((![X0 : $i]:
% 0.19/0.52          (~ (r2_hidden @ X0 @ sk_D_1)
% 0.19/0.52           | ~ (r1_tarski @ sk_D_1 @ sk_C)
% 0.19/0.52           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 0.19/0.52           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.19/0.52         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['59', '65'])).
% 0.19/0.52  thf('67', plain,
% 0.19/0.52      ((![X0 : $i]:
% 0.19/0.52          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 0.19/0.52           | ~ (r2_hidden @ X0 @ sk_D_1)))
% 0.19/0.52         <= (((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['58', '66'])).
% 0.19/0.52  thf('68', plain,
% 0.19/0.52      ((![X0 : $i]:
% 0.19/0.52          (~ (r2_hidden @ X0 @ sk_D_1)
% 0.19/0.52           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.19/0.52         <= (((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['57', '67'])).
% 0.19/0.52  thf('69', plain,
% 0.19/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.52         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.19/0.52             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['56', '68'])).
% 0.19/0.52  thf('70', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('71', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.19/0.52          | ~ (r2_hidden @ X4 @ (k1_tops_1 @ X5 @ X6))
% 0.19/0.52          | (m1_connsp_2 @ X6 @ X5 @ X4)
% 0.19/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.52          | ~ (l1_pre_topc @ X5)
% 0.19/0.52          | ~ (v2_pre_topc @ X5)
% 0.19/0.52          | (v2_struct_0 @ X5))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.52  thf('72', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.52  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('75', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v2_struct_0 @ sk_A)
% 0.19/0.52          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.19/0.52  thf('76', plain,
% 0.19/0.52      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.52         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.52         | (v2_struct_0 @ sk_A)))
% 0.19/0.52         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.19/0.52             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['69', '75'])).
% 0.19/0.52  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('78', plain,
% 0.19/0.52      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.19/0.52         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.19/0.52             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.52  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('80', plain,
% 0.19/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.52         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.19/0.52             ((r1_tarski @ sk_D_1 @ sk_C)) & 
% 0.19/0.52             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.19/0.52             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.52      inference('clc', [status(thm)], ['78', '79'])).
% 0.19/0.52  thf('81', plain,
% 0.19/0.52      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.52         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.52      inference('split', [status(esa)], ['6'])).
% 0.19/0.52  thf('82', plain,
% 0.19/0.52      (~ ((v3_pre_topc @ sk_D_1 @ sk_A)) | 
% 0.19/0.52       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.19/0.52       ~ ((r1_tarski @ sk_D_1 @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D_1)) | 
% 0.19/0.52       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.52  thf('83', plain, ($false),
% 0.19/0.52      inference('sat_resolution*', [status(thm)],
% 0.19/0.52                ['1', '3', '5', '7', '53', '55', '82'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
