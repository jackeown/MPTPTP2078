%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pK2lgBWeKL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:14 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 285 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  930 (2943 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('3',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('14',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('48',plain,(
    ! [X8: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,(
    ! [X8: $i] :
      ~ ( v1_subset_1 @ X8 @ X8 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','51'])).

thf('53',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('56',plain,(
    ! [X11: $i] :
      ( ( ( k2_pre_topc @ X11 @ ( k2_struct_0 @ X11 ) )
        = ( k2_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ X13 )
       != ( u1_struct_0 @ X14 ) )
      | ( v1_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('81',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('82',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','51','81'])).

thf('83',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['79','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pK2lgBWeKL
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 270 iterations in 0.126s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(t49_tex_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.39/0.58         ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.58             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.58            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58              ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.58                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.39/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d7_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i]:
% 0.39/0.58         (((X16) = (X15))
% 0.39/0.58          | (v1_subset_1 @ X16 @ X15)
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('split', [status(esa)], ['4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.39/0.58       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['4'])).
% 0.39/0.58  thf(dt_k2_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.58  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.58  thf('10', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(t43_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.39/0.58         ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X20 : $i, X21 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.58          | (v2_tex_2 @ X20 @ X21)
% 0.39/0.58          | ~ (l1_pre_topc @ X21)
% 0.39/0.58          | ~ (v1_tdlat_3 @ X21)
% 0.39/0.58          | ~ (v2_pre_topc @ X21)
% 0.39/0.58          | (v2_struct_0 @ X21))),
% 0.39/0.58      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_tdlat_3 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['4'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d7_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.58             ( ( v2_tex_2 @ B @ A ) & 
% 0.39/0.58               ( ![C:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.58                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.58          | ~ (v3_tex_2 @ X17 @ X18)
% 0.39/0.58          | ~ (v2_tex_2 @ X19 @ X18)
% 0.39/0.58          | ~ (r1_tarski @ X17 @ X19)
% 0.39/0.58          | ((X17) = (X19))
% 0.39/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.39/0.58          | ~ (l1_pre_topc @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | ((sk_B) = (X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.58          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | ((sk_B) = (X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.58          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.58           | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.58           | ((sk_B) = (X0))
% 0.39/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.58         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.39/0.58         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.39/0.58         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(t7_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58           ( ( ![D:$i]:
% 0.39/0.58               ( ( m1_subset_1 @ D @ A ) =>
% 0.39/0.58                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.39/0.58             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.58          | (r1_tarski @ X7 @ X5)
% 0.39/0.58          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 0.39/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.39/0.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.39/0.58          | (r1_tarski @ X1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (r2_hidden @ 
% 0.39/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(l3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ X3)
% 0.39/0.58          | (r2_hidden @ X2 @ X4)
% 0.39/0.58          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (r2_hidden @ 
% 0.39/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.39/0.58           (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('32', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.58          | (r1_tarski @ X7 @ X5)
% 0.39/0.58          | ~ (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X5)
% 0.39/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.39/0.58          | (r1_tarski @ X1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (r2_hidden @ 
% 0.39/0.58             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.39/0.58             (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '34'])).
% 0.39/0.58  thf('36', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['30', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.39/0.58         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.39/0.58         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['21', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | ~ (v1_tdlat_3 @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '37'])).
% 0.39/0.58  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('40', plain, ((v1_tdlat_3 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.39/0.58  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.39/0.58         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('split', [status(esa)], ['45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (((v1_subset_1 @ sk_B @ sk_B))
% 0.39/0.58         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.39/0.58             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['44', '46'])).
% 0.39/0.58  thf(fc14_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.39/0.58  thf('48', plain, (![X8 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X8) @ X8)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.39/0.58  thf('49', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.58  thf('50', plain, (![X8 : $i]: ~ (v1_subset_1 @ X8 @ X8)),
% 0.39/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.39/0.58       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['47', '50'])).
% 0.39/0.58  thf('52', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['7', '51'])).
% 0.39/0.58  thf('53', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['6', '52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_tdlat_3 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf(d3_struct_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf(t27_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (![X11 : $i]:
% 0.39/0.58         (((k2_pre_topc @ X11 @ (k2_struct_0 @ X11)) = (k2_struct_0 @ X11))
% 0.39/0.58          | ~ (l1_pre_topc @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('58', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(d2_tops_3, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v1_tops_1 @ B @ A ) <=>
% 0.39/0.58             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.58          | ((k2_pre_topc @ X14 @ X13) != (u1_struct_0 @ X14))
% 0.39/0.58          | (v1_tops_1 @ X13 @ X14)
% 0.39/0.58          | ~ (l1_pre_topc @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['57', '60'])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['56', '61'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ((k2_struct_0 @ X0) != (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['62'])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['55', '63'])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['64'])).
% 0.39/0.58  thf(dt_l1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.58      inference('clc', [status(thm)], ['65', '66'])).
% 0.39/0.58  thf('68', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(t48_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.39/0.58             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (![X22 : $i, X23 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.39/0.58          | (v3_tex_2 @ X22 @ X23)
% 0.39/0.58          | ~ (v2_tex_2 @ X22 @ X23)
% 0.39/0.58          | ~ (v1_tops_1 @ X22 @ X23)
% 0.39/0.58          | ~ (l1_pre_topc @ X23)
% 0.39/0.58          | ~ (v2_pre_topc @ X23)
% 0.39/0.58          | (v2_struct_0 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['67', '70'])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_tdlat_3 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['54', '72'])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_tdlat_3 @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['73'])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (((v3_tex_2 @ sk_B @ sk_A)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ~ (v1_tdlat_3 @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['53', '74'])).
% 0.39/0.58  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('77', plain, ((v1_tdlat_3 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('79', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['45'])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.39/0.58       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['45'])).
% 0.39/0.58  thf('82', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['7', '51', '81'])).
% 0.39/0.58  thf('83', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.39/0.58  thf('84', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['79', '83'])).
% 0.39/0.58  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
