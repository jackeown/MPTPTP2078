%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8ImRx3qn7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 297 expanded)
%              Number of leaves         :   24 (  93 expanded)
%              Depth                    :   24
%              Number of atoms          : 1328 (4795 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(demod,[status(thm)],['39','40','46'])).

thf('48',plain,
    ( ~ ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X20 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,
    ( ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

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

thf('66',plain,(
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

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_D )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_D )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('77',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
        | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
        | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','48','50','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8ImRx3qn7
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 326 iterations in 0.105s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(t8_connsp_2, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( ?[D:$i]:
% 0.36/0.56                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.56                     ( v3_pre_topc @ D @ A ) & 
% 0.36/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.56            ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56              ( ![C:$i]:
% 0.36/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                    ( ?[D:$i]:
% 0.36/0.56                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.56                        ( v3_pre_topc @ D @ A ) & 
% 0.36/0.56                        ( m1_subset_1 @
% 0.36/0.56                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (((r1_tarski @ sk_D @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (((r1_tarski @ sk_D @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['2'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X20 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56          | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56          | ~ (r2_hidden @ sk_B @ X20)
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      ((![X20 : $i]:
% 0.36/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56           | ~ (r2_hidden @ sk_B @ X20))) | 
% 0.36/0.56       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['2'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d1_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.56          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.36/0.56          | (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.56          | ~ (l1_pre_topc @ X15)
% 0.36/0.56          | ~ (v2_pre_topc @ X15)
% 0.36/0.56          | (v2_struct_0 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '12'])).
% 0.36/0.56  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.56  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t44_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X9 : $i, X10 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.56          | (r1_tarski @ (k1_tops_1 @ X10 @ X9) @ X9)
% 0.36/0.56          | ~ (l1_pre_topc @ X10))),
% 0.36/0.56      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.56  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.36/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ sk_C_1)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.36/0.56          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '25'])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t3_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X4 : $i, X5 : $i]:
% 0.36/0.56         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('29', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.36/0.56          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.36/0.56             (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['26', '31'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X4 : $i, X6 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      ((![X20 : $i]:
% 0.36/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56           | ~ (r2_hidden @ sk_B @ X20)))
% 0.36/0.56         <= ((![X20 : $i]:
% 0.36/0.56                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.36/0.56         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.36/0.56         <= ((![X20 : $i]:
% 0.36/0.56                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.56  thf('40', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.36/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(fc9_tops_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X7)
% 0.36/0.56          | ~ (v2_pre_topc @ X7)
% 0.36/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.56          | (v3_pre_topc @ (k1_tops_1 @ X7 @ X8) @ X7))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.36/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.56  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('46', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.36/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= ((![X20 : $i]:
% 0.36/0.56                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.36/0.56      inference('demod', [status(thm)], ['39', '40', '46'])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (~
% 0.36/0.56       (![X20 : $i]:
% 0.36/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.36/0.56           | ~ (r2_hidden @ sk_B @ X20))) | 
% 0.36/0.56       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['49'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.36/0.56      inference('split', [status(esa)], ['2'])).
% 0.36/0.56  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['49'])).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_C_1)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['54', '57'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((r1_tarski @ sk_D @ X0)
% 0.36/0.56           | (r2_hidden @ (sk_C @ X0 @ sk_D) @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      ((((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X4 : $i, X6 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.56  thf(t5_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.36/0.56                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.36/0.56          | ~ (v3_pre_topc @ X17 @ X18)
% 0.36/0.56          | ~ (r2_hidden @ X19 @ X17)
% 0.36/0.56          | (m1_connsp_2 @ X17 @ X18 @ X19)
% 0.36/0.56          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.36/0.56          | ~ (l1_pre_topc @ X18)
% 0.36/0.56          | ~ (v2_pre_topc @ X18)
% 0.36/0.56          | (v2_struct_0 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((v2_struct_0 @ sk_A)
% 0.36/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.56           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((v2_struct_0 @ sk_A)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.56           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.56           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56           | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)) & ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '70'])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A)
% 0.36/0.56         | (m1_connsp_2 @ sk_D @ sk_A @ sk_B)
% 0.36/0.56         | ~ (r2_hidden @ sk_B @ sk_D)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)) & ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['52', '71'])).
% 0.36/0.56  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (((~ (r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)) & ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_D @ sk_A @ sk_B))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['51', '74'])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.56  thf('77', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.56          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.36/0.56          | (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.56          | ~ (l1_pre_topc @ X15)
% 0.36/0.56          | ~ (v2_pre_topc @ X15)
% 0.36/0.56          | (v2_struct_0 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((v2_struct_0 @ sk_A)
% 0.36/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.36/0.56           | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.36/0.56  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((v2_struct_0 @ sk_A)
% 0.36/0.56           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.36/0.56           | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.36/0.56  thf('82', plain,
% 0.36/0.56      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['75', '81'])).
% 0.36/0.56  thf('83', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['82', '83'])).
% 0.36/0.56  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['84', '85'])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.56  thf(t48_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( r1_tarski @ B @ C ) =>
% 0.36/0.56                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.36/0.56          | ~ (r1_tarski @ X11 @ X13)
% 0.36/0.56          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ (k1_tops_1 @ X12 @ X13))
% 0.36/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.36/0.56          | ~ (l1_pre_topc @ X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (l1_pre_topc @ sk_A)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56           | ~ (r1_tarski @ sk_D @ X0)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.56  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('92', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56           | ~ (r1_tarski @ sk_D @ X0)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['90', '91'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      (((~ (r1_tarski @ sk_D @ sk_C_1)
% 0.36/0.56         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['87', '92'])).
% 0.36/0.56  thf('94', plain,
% 0.36/0.56      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.36/0.56  thf('96', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('97', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 0.36/0.56         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.56  thf('98', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['86', '97'])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('100', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.56          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.36/0.56          | (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.56          | ~ (l1_pre_topc @ X15)
% 0.36/0.56          | ~ (v2_pre_topc @ X15)
% 0.36/0.56          | (v2_struct_0 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.36/0.56  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['98', '104'])).
% 0.36/0.56  thf('106', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.36/0.56  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('109', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.56         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.36/0.56             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_D @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['107', '108'])).
% 0.36/0.56  thf('110', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.56         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('111', plain,
% 0.36/0.56      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.36/0.56       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.36/0.56       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_D @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.36/0.56  thf('112', plain, ($false),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['1', '3', '5', '48', '50', '111'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
