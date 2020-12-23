%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCLgpdrRQn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 339 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  643 (4062 expanded)
%              Number of equality atoms :   15 ( 139 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t28_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( v2_compts_1 @ C @ A )
                      <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_compts_1])).

thf('0',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ( ( sk_D @ X16 @ X14 )
        = X16 )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( sk_D @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( sk_D @ sk_C_1 @ sk_B )
      = sk_C_1 )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ( sk_D @ sk_C_1 @ sk_B )
      = sk_C_1 )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X16 @ X14 ) @ X14 )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C_1 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
      | ( v2_compts_1 @ sk_C_1 @ sk_A ) )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ( v2_compts_1 @ sk_C_1 @ sk_B )
   <= ~ ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','50'])).

thf('52',plain,(
    ~ ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','51'])).

thf('53',plain,(
    ~ ( v2_compts_1 @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['3','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ~ ( v2_compts_1 @ X16 @ X15 )
      | ( X17 != X16 )
      | ( v2_compts_1 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_compts_1 @ X16 @ X14 )
      | ~ ( v2_compts_1 @ X16 @ X15 )
      | ~ ( r1_tarski @ X16 @ ( k2_struct_0 @ X14 ) )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C_1 @ sk_A )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
   <= ( v2_compts_1 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('62',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('63',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','51','62'])).

thf('64',plain,(
    v2_compts_1 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ X0 ) )
      | ( v2_compts_1 @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','64'])).

thf('66',plain,
    ( ( v2_compts_1 @ sk_C_1 @ sk_B )
    | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('68',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_compts_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCLgpdrRQn
% 0.16/0.38  % Computer   : n011.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:45:57 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 113 iterations in 0.040s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.25/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.25/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.25/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.25/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.53  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.25/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.53  thf(t28_compts_1, conjecture,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_pre_topc @ A ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.53           ( ![C:$i]:
% 0.25/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.53               ( ![D:$i]:
% 0.25/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.53                   ( ( ( C ) = ( D ) ) =>
% 0.25/0.53                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i]:
% 0.25/0.53        ( ( l1_pre_topc @ A ) =>
% 0.25/0.53          ( ![B:$i]:
% 0.25/0.53            ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.53              ( ![C:$i]:
% 0.25/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.53                  ( ![D:$i]:
% 0.25/0.53                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.53                      ( ( ( C ) = ( D ) ) =>
% 0.25/0.53                        ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t28_compts_1])).
% 0.25/0.53  thf('0', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_D_1 @ sk_B) | ~ (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('1', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_D_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('2', plain, (((sk_C_1) = (sk_D_1))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('3', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.25/0.53  thf('4', plain,
% 0.25/0.53      (~ ((v2_compts_1 @ sk_D_1 @ sk_B)) | ~ ((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('5', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_D_1 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('6', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_D_1 @ sk_B)) <= (((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.25/0.53      inference('split', [status(esa)], ['5'])).
% 0.25/0.53  thf('7', plain, (((sk_C_1) = (sk_D_1))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('8', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_C_1 @ sk_B)) <= (((v2_compts_1 @ sk_D_1 @ sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.53  thf(d3_struct_0, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.25/0.53  thf('9', plain,
% 0.25/0.53      (![X7 : $i]:
% 0.25/0.53         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.25/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.25/0.53  thf(d3_tarski, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.53  thf('10', plain,
% 0.25/0.53      (![X1 : $i, X3 : $i]:
% 0.25/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.25/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('12', plain, (((sk_C_1) = (sk_D_1))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('13', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.25/0.53  thf(l3_subset_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.25/0.53  thf('14', plain,
% 0.25/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X4 @ X5)
% 0.25/0.53          | (r2_hidden @ X4 @ X6)
% 0.25/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.25/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.25/0.53  thf('15', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.25/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.25/0.53  thf('16', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((r1_tarski @ sk_C_1 @ X0)
% 0.25/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['10', '15'])).
% 0.25/0.53  thf('17', plain,
% 0.25/0.53      (![X1 : $i, X3 : $i]:
% 0.25/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.25/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.53  thf('18', plain,
% 0.25/0.53      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_B))
% 0.25/0.53        | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.25/0.53  thf('19', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.25/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.25/0.53      inference('sup+', [status(thm)], ['9', '19'])).
% 0.25/0.53  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(dt_m1_pre_topc, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_pre_topc @ A ) =>
% 0.25/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.25/0.53  thf('22', plain,
% 0.25/0.53      (![X9 : $i, X10 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X9 @ X10)
% 0.25/0.53          | (l1_pre_topc @ X9)
% 0.25/0.53          | ~ (l1_pre_topc @ X10))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.25/0.53  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.25/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.53  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.25/0.53  thf(dt_l1_pre_topc, axiom,
% 0.25/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.25/0.53  thf('26', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.25/0.53  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.25/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.25/0.53  thf('28', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.25/0.53      inference('demod', [status(thm)], ['20', '27'])).
% 0.25/0.53  thf('29', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(t11_compts_1, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_pre_topc @ A ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.53           ( ![C:$i]:
% 0.25/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.53               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.25/0.53                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.25/0.53                   ( ![D:$i]:
% 0.25/0.53                     ( ( m1_subset_1 @
% 0.25/0.53                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.53                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.53  thf('30', plain,
% 0.25/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.25/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.25/0.53          | ((sk_D @ X16 @ X14) = (X16))
% 0.25/0.53          | (v2_compts_1 @ X16 @ X15)
% 0.25/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.25/0.53          | ~ (l1_pre_topc @ X15))),
% 0.25/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.25/0.53  thf('31', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (l1_pre_topc @ sk_A)
% 0.25/0.53          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | ((sk_D @ sk_C_1 @ X0) = (sk_C_1))
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.25/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('33', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | ((sk_D @ sk_C_1 @ X0) = (sk_C_1))
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.25/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.53  thf('34', plain,
% 0.25/0.53      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.25/0.53        | ((sk_D @ sk_C_1 @ sk_B) = (sk_C_1))
% 0.25/0.53        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.25/0.53  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('36', plain,
% 0.25/0.53      ((((sk_D @ sk_C_1 @ sk_B) = (sk_C_1)) | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.25/0.53  thf('37', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('38', plain,
% 0.25/0.53      ((((sk_D @ sk_C_1 @ sk_B) = (sk_C_1)))
% 0.25/0.53         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.53  thf('39', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.25/0.53      inference('demod', [status(thm)], ['20', '27'])).
% 0.25/0.53  thf('40', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('41', plain,
% 0.25/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.25/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.25/0.53          | ~ (v2_compts_1 @ (sk_D @ X16 @ X14) @ X14)
% 0.25/0.53          | (v2_compts_1 @ X16 @ X15)
% 0.25/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.25/0.53          | ~ (l1_pre_topc @ X15))),
% 0.25/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.25/0.53  thf('42', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (l1_pre_topc @ sk_A)
% 0.25/0.53          | (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | ~ (v2_compts_1 @ (sk_D @ sk_C_1 @ X0) @ X0)
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.25/0.53  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('44', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | ~ (v2_compts_1 @ (sk_D @ sk_C_1 @ X0) @ X0)
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.25/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.25/0.53  thf('45', plain,
% 0.25/0.53      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.25/0.53        | ~ (v2_compts_1 @ (sk_D @ sk_C_1 @ sk_B) @ sk_B)
% 0.25/0.53        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['39', '44'])).
% 0.25/0.53  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('47', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ (sk_D @ sk_C_1 @ sk_B) @ sk_B)
% 0.25/0.53        | (v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.25/0.53  thf('48', plain,
% 0.25/0.53      (((~ (v2_compts_1 @ sk_C_1 @ sk_B) | (v2_compts_1 @ sk_C_1 @ sk_A)))
% 0.25/0.53         <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['38', '47'])).
% 0.25/0.53  thf('49', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_C_1 @ sk_A)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('50', plain,
% 0.25/0.53      ((~ (v2_compts_1 @ sk_C_1 @ sk_B)) <= (~ ((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('clc', [status(thm)], ['48', '49'])).
% 0.25/0.53  thf('51', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ~ ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.25/0.53      inference('sup-', [status(thm)], ['8', '50'])).
% 0.25/0.53  thf('52', plain, (~ ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.25/0.53      inference('sat_resolution*', [status(thm)], ['4', '51'])).
% 0.25/0.53  thf('53', plain, (~ (v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.25/0.53      inference('simpl_trail', [status(thm)], ['3', '52'])).
% 0.25/0.53  thf('54', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.25/0.53  thf('55', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('56', plain,
% 0.25/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X14 @ X15)
% 0.25/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.25/0.53          | ~ (v2_compts_1 @ X16 @ X15)
% 0.25/0.53          | ((X17) != (X16))
% 0.25/0.53          | (v2_compts_1 @ X17 @ X14)
% 0.25/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.25/0.53          | ~ (l1_pre_topc @ X15))),
% 0.25/0.53      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.25/0.53  thf('57', plain,
% 0.25/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.53         (~ (l1_pre_topc @ X15)
% 0.25/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.25/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.53          | (v2_compts_1 @ X16 @ X14)
% 0.25/0.53          | ~ (v2_compts_1 @ X16 @ X15)
% 0.25/0.53          | ~ (r1_tarski @ X16 @ (k2_struct_0 @ X14))
% 0.25/0.53          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.25/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.25/0.53  thf('58', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.25/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.25/0.53          | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['55', '57'])).
% 0.25/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('60', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | ~ (v2_compts_1 @ sk_C_1 @ sk_A)
% 0.25/0.53          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.25/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.25/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.25/0.53  thf('61', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_C_1 @ sk_A)) <= (((v2_compts_1 @ sk_C_1 @ sk_A)))),
% 0.25/0.53      inference('split', [status(esa)], ['5'])).
% 0.25/0.53  thf('62', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_C_1 @ sk_A)) | ((v2_compts_1 @ sk_D_1 @ sk_B))),
% 0.25/0.53      inference('split', [status(esa)], ['5'])).
% 0.25/0.53  thf('63', plain, (((v2_compts_1 @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('sat_resolution*', [status(thm)], ['4', '51', '62'])).
% 0.25/0.53  thf('64', plain, ((v2_compts_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.25/0.53  thf('65', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.53          | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ X0))
% 0.25/0.53          | (v2_compts_1 @ sk_C_1 @ X0)
% 0.25/0.53          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.25/0.53      inference('demod', [status(thm)], ['60', '64'])).
% 0.25/0.53  thf('66', plain,
% 0.25/0.53      (((v2_compts_1 @ sk_C_1 @ sk_B)
% 0.25/0.53        | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))
% 0.25/0.53        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['54', '65'])).
% 0.25/0.53  thf('67', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_B))),
% 0.25/0.53      inference('demod', [status(thm)], ['20', '27'])).
% 0.25/0.53  thf('68', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('69', plain, ((v2_compts_1 @ sk_C_1 @ sk_B)),
% 0.25/0.53      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.25/0.53  thf('70', plain, ($false), inference('demod', [status(thm)], ['53', '69'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
