%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdV5PZWzgt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:18 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  180 (1680 expanded)
%              Number of leaves         :   28 ( 460 expanded)
%              Depth                    :   20
%              Number of atoms          : 1953 (21375 expanded)
%              Number of equality atoms :   51 ( 245 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_subset_1 @ X16 @ X15 )
      | ( X16 != X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('49',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_subset_1 @ X15 @ X15 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v1_subset_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','51','52'])).

thf('54',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('57',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','51'])).

thf('61',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ( r2_hidden @ ( sk_D_1 @ X6 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( sk_C @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','99'])).

thf('101',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('102',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['105','106','115'])).

thf('117',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['102','116'])).

thf('118',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('119',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','51'])).

thf('121',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('123',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('125',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('130',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('131',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['100','101','125','126','127','128','129','130','131'])).

thf('133',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('135',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( X17
       != ( sk_C @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
     != ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','137'])).

thf('139',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['113','114'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('142',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('143',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('144',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143'])).

thf('145',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('146',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['132','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['54','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdV5PZWzgt
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:41 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 399 iterations in 0.224s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.70  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.48/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.48/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.70  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.48/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.70  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.48/0.70  thf(t49_tex_2, conjecture,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.48/0.70         ( l1_pre_topc @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.70             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i]:
% 0.48/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.70            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.70          ( ![B:$i]:
% 0.48/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70              ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.70                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.48/0.70  thf('0', plain,
% 0.48/0.70      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.48/0.70        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.48/0.70        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.48/0.70       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf(t2_tsep_1, axiom,
% 0.48/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.48/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.48/0.70  thf(t1_tsep_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( l1_pre_topc @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.48/0.70           ( m1_subset_1 @
% 0.48/0.70             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X12 : $i, X13 : $i]:
% 0.48/0.70         (~ (m1_pre_topc @ X12 @ X13)
% 0.48/0.70          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.48/0.70          | ~ (l1_pre_topc @ X13))),
% 0.48/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.48/0.70  thf('6', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.70  thf('7', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf(t43_tex_2, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.48/0.70         ( l1_pre_topc @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      (![X20 : $i, X21 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.70          | (v2_tex_2 @ X20 @ X21)
% 0.48/0.70          | ~ (l1_pre_topc @ X21)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X21)
% 0.48/0.70          | ~ (v2_pre_topc @ X21)
% 0.48/0.70          | (v2_struct_0 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('10', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.70  thf('11', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(d7_tex_2, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( l1_pre_topc @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70           ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.70             ( ( v2_tex_2 @ B @ A ) & 
% 0.48/0.70               ( ![C:$i]:
% 0.48/0.70                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.70                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.48/0.70                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (v3_tex_2 @ X17 @ X18)
% 0.48/0.70          | ~ (v2_tex_2 @ X19 @ X18)
% 0.48/0.70          | ~ (r1_tarski @ X17 @ X19)
% 0.48/0.70          | ((X17) = (X19))
% 0.48/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (l1_pre_topc @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ sk_A)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70          | ((sk_B) = (X0))
% 0.48/0.70          | ~ (r1_tarski @ sk_B @ X0)
% 0.48/0.70          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.48/0.70          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.70  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70          | ((sk_B) = (X0))
% 0.48/0.70          | ~ (r1_tarski @ sk_B @ X0)
% 0.48/0.70          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.48/0.70          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.48/0.70           | ~ (r1_tarski @ sk_B @ X0)
% 0.48/0.70           | ((sk_B) = (X0))
% 0.48/0.70           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.48/0.70         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['12', '17'])).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.48/0.70         | ((sk_B) = (u1_struct_0 @ sk_A))
% 0.48/0.70         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.48/0.70         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.48/0.70         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['11', '18'])).
% 0.48/0.70  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t3_subset, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      (![X9 : $i, X10 : $i]:
% 0.48/0.70         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('23', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.48/0.70         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.48/0.70         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.48/0.70         | (v2_struct_0 @ sk_A)
% 0.48/0.70         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.70         | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.70         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['10', '24'])).
% 0.48/0.70  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.48/0.70         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.48/0.70  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.48/0.70      inference('clc', [status(thm)], ['29', '30'])).
% 0.48/0.70  thf('32', plain,
% 0.48/0.70      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.48/0.70         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (((v1_subset_1 @ sk_B @ sk_B))
% 0.48/0.70         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.48/0.70             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t7_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ![C:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70           ( ( ![D:$i]:
% 0.48/0.70               ( ( m1_subset_1 @ D @ A ) =>
% 0.48/0.70                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.48/0.70             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.48/0.70  thf('36', plain,
% 0.48/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.48/0.70          | (r1_tarski @ X5 @ X3)
% 0.48/0.70          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.48/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.48/0.70          | (r1_tarski @ X0 @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (((r1_tarski @ sk_B @ sk_B)
% 0.48/0.70        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['34', '37'])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.48/0.70          | (r1_tarski @ X5 @ X3)
% 0.48/0.70          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.48/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.48/0.70  thf('41', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.48/0.70          | (r1_tarski @ X0 @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (((r1_tarski @ sk_B @ sk_B)
% 0.48/0.70        | (r1_tarski @ sk_B @ sk_B)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['38', '41'])).
% 0.48/0.70  thf('43', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('44', plain, (((r1_tarski @ sk_B @ sk_B) | (r1_tarski @ sk_B @ sk_B))),
% 0.48/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.48/0.70  thf('45', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.48/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (![X9 : $i, X11 : $i]:
% 0.48/0.70         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('47', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.48/0.70  thf(d7_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X15 : $i, X16 : $i]:
% 0.48/0.70         (~ (v1_subset_1 @ X16 @ X15)
% 0.48/0.70          | ((X16) != (X15))
% 0.48/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (![X15 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))
% 0.48/0.70          | ~ (v1_subset_1 @ X15 @ X15))),
% 0.48/0.70      inference('simplify', [status(thm)], ['48'])).
% 0.48/0.70  thf('50', plain, (~ (v1_subset_1 @ sk_B @ sk_B)),
% 0.48/0.70      inference('sup-', [status(thm)], ['47', '49'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.48/0.70       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['33', '50'])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.48/0.70       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('split', [status(esa)], ['0'])).
% 0.48/0.70  thf('53', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('sat_resolution*', [status(thm)], ['3', '51', '52'])).
% 0.48/0.70  thf('54', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (![X15 : $i, X16 : $i]:
% 0.48/0.70         (((X16) = (X15))
% 0.48/0.70          | (v1_subset_1 @ X16 @ X15)
% 0.48/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.48/0.70        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.48/0.70  thf('58', plain,
% 0.48/0.70      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.48/0.70         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('split', [status(esa)], ['2'])).
% 0.48/0.70  thf('59', plain,
% 0.48/0.70      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.48/0.70         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.48/0.70  thf('60', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('sat_resolution*', [status(thm)], ['3', '51'])).
% 0.48/0.70  thf('61', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.70  thf('63', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf('64', plain,
% 0.48/0.70      (![X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (v2_tex_2 @ X17 @ X18)
% 0.48/0.70          | (m1_subset_1 @ (sk_C @ X17 @ X18) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | (v3_tex_2 @ X17 @ X18)
% 0.48/0.70          | ~ (l1_pre_topc @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.48/0.70  thf('66', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['65'])).
% 0.48/0.70  thf('67', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['62', '66'])).
% 0.48/0.70  thf('68', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.70  thf('69', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf(t8_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ![C:$i]:
% 0.48/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70           ( ( ![D:$i]:
% 0.48/0.70               ( ( m1_subset_1 @ D @ A ) =>
% 0.48/0.70                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.48/0.70             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.48/0.70  thf('70', plain,
% 0.48/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.48/0.70          | ((X8) = (X6))
% 0.48/0.70          | (r2_hidden @ (sk_D_1 @ X6 @ X8 @ X7) @ X8)
% 0.48/0.70          | (r2_hidden @ (sk_D_1 @ X6 @ X8 @ X7) @ X6)
% 0.48/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.48/0.70  thf('71', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)) @ X1)
% 0.48/0.70          | ((X1) = (u1_struct_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.48/0.70  thf('72', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['68', '71'])).
% 0.48/0.70  thf('73', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((r2_hidden @ 
% 0.48/0.70           (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70            (u1_struct_0 @ X0)) @ 
% 0.48/0.70           (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['72'])).
% 0.48/0.70  thf('74', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.70  thf(l3_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.48/0.70  thf('75', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.70          | (r2_hidden @ X0 @ X2)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.48/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.48/0.70  thf('76', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (r2_hidden @ X1 @ (sk_C @ (u1_struct_0 @ X0) @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.48/0.70  thf('77', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['73', '76'])).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((r2_hidden @ 
% 0.48/0.70           (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70            (u1_struct_0 @ X0)) @ 
% 0.48/0.70           (u1_struct_0 @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['77'])).
% 0.48/0.70  thf('79', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.70  thf('80', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf('81', plain,
% 0.48/0.70      (![X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (v2_tex_2 @ X17 @ X18)
% 0.48/0.70          | (r1_tarski @ X17 @ (sk_C @ X17 @ X18))
% 0.48/0.70          | (v3_tex_2 @ X17 @ X18)
% 0.48/0.70          | ~ (l1_pre_topc @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.70  thf('82', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.48/0.70  thf('83', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['82'])).
% 0.48/0.70  thf('84', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['79', '83'])).
% 0.48/0.70  thf('85', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['84'])).
% 0.48/0.70  thf('86', plain,
% 0.48/0.70      (![X9 : $i, X11 : $i]:
% 0.48/0.70         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('87', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['85', '86'])).
% 0.48/0.70  thf('88', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.70          | (r2_hidden @ X0 @ X2)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.48/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.48/0.70  thf('89', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (r2_hidden @ X1 @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['87', '88'])).
% 0.48/0.70  thf('90', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (r2_hidden @ 
% 0.48/0.70             (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70              (u1_struct_0 @ X0)) @ 
% 0.48/0.70             (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['78', '89'])).
% 0.48/0.70  thf('91', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((r2_hidden @ 
% 0.48/0.70           (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70            (u1_struct_0 @ X0)) @ 
% 0.48/0.70           (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['90'])).
% 0.48/0.70  thf('92', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((r2_hidden @ 
% 0.48/0.70           (sk_D_1 @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70            (u1_struct_0 @ X0)) @ 
% 0.48/0.70           (u1_struct_0 @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['77'])).
% 0.48/0.70  thf('93', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf('94', plain,
% 0.48/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.48/0.70          | ((X8) = (X6))
% 0.48/0.70          | ~ (r2_hidden @ (sk_D_1 @ X6 @ X8 @ X7) @ X8)
% 0.48/0.70          | ~ (r2_hidden @ (sk_D_1 @ X6 @ X8 @ X7) @ X6)
% 0.48/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.48/0.70  thf('95', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (r2_hidden @ 
% 0.48/0.70               (sk_D_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)) @ 
% 0.48/0.70               (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (r2_hidden @ 
% 0.48/0.70               (sk_D_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)) @ X1)
% 0.48/0.70          | ((X1) = (u1_struct_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['93', '94'])).
% 0.48/0.70  thf('96', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (r2_hidden @ 
% 0.48/0.70               (sk_D_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70                (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)) @ 
% 0.48/0.70               (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['92', '95'])).
% 0.48/0.70  thf('97', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (r2_hidden @ 
% 0.48/0.70               (sk_D_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70                (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)) @ 
% 0.48/0.70               (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['96'])).
% 0.48/0.70  thf('98', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['91', '97'])).
% 0.48/0.70  thf('99', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.48/0.70          | ~ (v2_pre_topc @ X0)
% 0.48/0.70          | (v2_struct_0 @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['98'])).
% 0.48/0.70  thf('100', plain,
% 0.48/0.70      ((~ (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | (v2_struct_0 @ sk_A)
% 0.48/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.70        | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.70        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.48/0.70        | ((sk_C @ (u1_struct_0 @ sk_A) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '99'])).
% 0.48/0.70  thf('101', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('102', plain,
% 0.48/0.70      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.48/0.70         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.48/0.70  thf('103', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('104', plain,
% 0.48/0.70      (![X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (v2_tex_2 @ X17 @ X18)
% 0.48/0.70          | (m1_subset_1 @ (sk_C @ X17 @ X18) @ 
% 0.48/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | (v3_tex_2 @ X17 @ X18)
% 0.48/0.70          | ~ (l1_pre_topc @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.70  thf('105', plain,
% 0.48/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | (v3_tex_2 @ sk_B @ sk_A)
% 0.48/0.70        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.70        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['103', '104'])).
% 0.48/0.70  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('107', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('108', plain,
% 0.48/0.70      (![X20 : $i, X21 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.48/0.70          | (v2_tex_2 @ X20 @ X21)
% 0.48/0.70          | ~ (l1_pre_topc @ X21)
% 0.48/0.70          | ~ (v1_tdlat_3 @ X21)
% 0.48/0.70          | ~ (v2_pre_topc @ X21)
% 0.48/0.70          | (v2_struct_0 @ X21))),
% 0.48/0.70      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.48/0.70  thf('109', plain,
% 0.48/0.70      (((v2_struct_0 @ sk_A)
% 0.48/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.70        | ~ (v1_tdlat_3 @ sk_A)
% 0.48/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['107', '108'])).
% 0.48/0.70  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('111', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('113', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.48/0.70      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.48/0.70  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('115', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.48/0.70      inference('clc', [status(thm)], ['113', '114'])).
% 0.48/0.70  thf('116', plain,
% 0.48/0.70      (((v3_tex_2 @ sk_B @ sk_A)
% 0.48/0.70        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('demod', [status(thm)], ['105', '106', '115'])).
% 0.48/0.70  thf('117', plain,
% 0.48/0.70      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.48/0.70         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.48/0.70         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup+', [status(thm)], ['102', '116'])).
% 0.48/0.70  thf('118', plain,
% 0.48/0.70      (![X9 : $i, X10 : $i]:
% 0.48/0.70         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('119', plain,
% 0.48/0.70      ((((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)))
% 0.48/0.70         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['117', '118'])).
% 0.48/0.70  thf('120', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.48/0.70      inference('sat_resolution*', [status(thm)], ['3', '51'])).
% 0.48/0.70  thf('121', plain,
% 0.48/0.70      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.48/0.70  thf('122', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.48/0.70  thf('123', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.48/0.70      inference('clc', [status(thm)], ['121', '122'])).
% 0.48/0.70  thf('124', plain,
% 0.48/0.70      (![X9 : $i, X11 : $i]:
% 0.48/0.70         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.48/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.70  thf('125', plain,
% 0.48/0.70      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['123', '124'])).
% 0.48/0.70  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('128', plain, ((v1_tdlat_3 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('129', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('130', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('131', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('132', plain,
% 0.48/0.70      (((v2_struct_0 @ sk_A)
% 0.48/0.70        | (v3_tex_2 @ sk_B @ sk_A)
% 0.48/0.70        | ((sk_C @ sk_B @ sk_A) = (sk_B)))),
% 0.48/0.70      inference('demod', [status(thm)],
% 0.48/0.70                ['100', '101', '125', '126', '127', '128', '129', '130', '131'])).
% 0.48/0.70  thf('133', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('134', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.48/0.70  thf('135', plain,
% 0.48/0.70      (![X17 : $i, X18 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.70          | ~ (v2_tex_2 @ X17 @ X18)
% 0.48/0.70          | ((X17) != (sk_C @ X17 @ X18))
% 0.48/0.70          | (v3_tex_2 @ X17 @ X18)
% 0.48/0.70          | ~ (l1_pre_topc @ X18))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.70  thf('136', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (l1_pre_topc @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0)
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((u1_struct_0 @ X0) != (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['134', '135'])).
% 0.48/0.70  thf('137', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ((u1_struct_0 @ X0) != (sk_C @ (u1_struct_0 @ X0) @ X0))
% 0.48/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.48/0.70          | ~ (l1_pre_topc @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['136'])).
% 0.48/0.70  thf('138', plain,
% 0.48/0.70      ((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.48/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.70        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.48/0.70        | ((u1_struct_0 @ sk_A) != (sk_C @ (u1_struct_0 @ sk_A) @ sk_A)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['133', '137'])).
% 0.48/0.70  thf('139', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.48/0.70      inference('clc', [status(thm)], ['113', '114'])).
% 0.48/0.70  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('141', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('142', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.70  thf('143', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.48/0.71      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.48/0.71  thf('144', plain,
% 0.48/0.71      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)],
% 0.48/0.71                ['138', '139', '140', '141', '142', '143'])).
% 0.48/0.71  thf('145', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.48/0.71      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.48/0.71  thf('146', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.48/0.71      inference('clc', [status(thm)], ['144', '145'])).
% 0.48/0.71  thf('147', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['132', '146'])).
% 0.48/0.71  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('149', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.48/0.71      inference('clc', [status(thm)], ['147', '148'])).
% 0.48/0.71  thf('150', plain, ($false), inference('demod', [status(thm)], ['54', '149'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.55/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
