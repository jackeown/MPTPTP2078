%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U7Gs1k2W9V

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:16 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 420 expanded)
%              Number of leaves         :   36 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          : 1085 (4497 expanded)
%              Number of equality atoms :   29 (  90 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('3',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_tdlat_3 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_B_1 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
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
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('48',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ X10 @ X10 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','51'])).

thf('53',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_tdlat_3 @ X23 )
      | ( v3_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ X16 )
       != ( u1_struct_0 @ X17 ) )
      | ( v1_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v1_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_tdlat_3 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','52'])).

thf('93',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','88','89','90','91','92'])).

thf('94',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('95',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('96',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','51','95'])).

thf('97',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['93','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U7Gs1k2W9V
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 331 iterations in 0.240s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.70  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.70  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.47/0.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.47/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.47/0.70  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.47/0.70  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.47/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.70  thf(t49_tex_2, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.47/0.70         ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.70             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.70            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70          ( ![B:$i]:
% 0.47/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70              ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.70                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.47/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(d7_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X18 : $i, X19 : $i]:
% 0.47/0.70         (((X19) = (X18))
% 0.47/0.70          | (v1_subset_1 @ X19 @ X18)
% 0.47/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.70         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.70      inference('split', [status(esa)], ['4'])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.70         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.47/0.70       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('split', [status(esa)], ['4'])).
% 0.47/0.70  thf(dt_k2_subset_1, axiom,
% 0.47/0.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.47/0.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.70  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.70  thf('10', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(t43_tex_2, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.47/0.70         ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.70          | (v2_tex_2 @ X25 @ X26)
% 0.47/0.70          | ~ (l1_pre_topc @ X26)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X26)
% 0.47/0.70          | ~ (v2_pre_topc @ X26)
% 0.47/0.70          | (v2_struct_0 @ X26))),
% 0.47/0.70      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf('13', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['4'])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(d7_tex_2, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.70             ( ( v2_tex_2 @ B @ A ) & 
% 0.47/0.70               ( ![C:$i]:
% 0.47/0.70                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.70                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.47/0.70          | ~ (v3_tex_2 @ X20 @ X21)
% 0.47/0.70          | ~ (v2_tex_2 @ X22 @ X21)
% 0.47/0.70          | ~ (r1_tarski @ X20 @ X22)
% 0.47/0.70          | ((X20) = (X22))
% 0.47/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.47/0.70          | ~ (l1_pre_topc @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ sk_A)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.70          | ((sk_B_1) = (X0))
% 0.47/0.70          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.70          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.70          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.70  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.70          | ((sk_B_1) = (X0))
% 0.47/0.70          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.70          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.70          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      ((![X0 : $i]:
% 0.47/0.70          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.70           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.70           | ((sk_B_1) = (X0))
% 0.47/0.70           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.47/0.70         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['13', '20'])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('23', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(t7_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70           ( ( ![D:$i]:
% 0.47/0.70               ( ( m1_subset_1 @ D @ A ) =>
% 0.47/0.70                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.47/0.70             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.47/0.70          | (r1_tarski @ X9 @ X7)
% 0.47/0.70          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.47/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.47/0.70          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.47/0.70          | (r1_tarski @ X1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | (r2_hidden @ 
% 0.47/0.70           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.70           sk_B_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(l3_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X4 @ X5)
% 0.47/0.70          | (r2_hidden @ X4 @ X6)
% 0.47/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.47/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | (r2_hidden @ 
% 0.47/0.70           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.70           (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['26', '29'])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('32', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.47/0.70          | (r1_tarski @ X9 @ X7)
% 0.47/0.70          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.47/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.47/0.70          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.47/0.70          | (r1_tarski @ X1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | ~ (r2_hidden @ 
% 0.47/0.70             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.70             (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['31', '34'])).
% 0.47/0.70  thf('36', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.70      inference('clc', [status(thm)], ['30', '35'])).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.47/0.70         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['21', '36'])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.70         | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.70         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70         | (v2_struct_0 @ sk_A)
% 0.47/0.70         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '37'])).
% 0.47/0.70  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('40', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.47/0.70  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('44', plain,
% 0.47/0.70      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('clc', [status(thm)], ['42', '43'])).
% 0.47/0.70  thf('45', plain,
% 0.47/0.70      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.70        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('46', plain,
% 0.47/0.70      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.70         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.70      inference('split', [status(esa)], ['45'])).
% 0.47/0.70  thf('47', plain,
% 0.47/0.70      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.47/0.70         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.47/0.70             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.70      inference('sup+', [status(thm)], ['44', '46'])).
% 0.47/0.70  thf(fc14_subset_1, axiom,
% 0.47/0.70    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.47/0.70  thf('48', plain, (![X10 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X10) @ X10)),
% 0.47/0.70      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.47/0.70  thf('49', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.47/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.70  thf('50', plain, (![X10 : $i]: ~ (v1_subset_1 @ X10 @ X10)),
% 0.47/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.70  thf('51', plain,
% 0.47/0.70      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.47/0.70       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['47', '50'])).
% 0.47/0.70  thf('52', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['7', '51'])).
% 0.47/0.70  thf('53', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['6', '52'])).
% 0.47/0.70  thf('54', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(dt_k3_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.70  thf('55', plain,
% 0.47/0.70      (![X2 : $i, X3 : $i]:
% 0.47/0.70         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.47/0.70          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.47/0.70  thf('56', plain,
% 0.47/0.70      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.70  thf(t17_tdlat_3, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ( v1_tdlat_3 @ A ) <=>
% 0.47/0.70         ( ![B:$i]:
% 0.47/0.70           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.47/0.70  thf('57', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i]:
% 0.47/0.70         (~ (v1_tdlat_3 @ X23)
% 0.47/0.70          | (v3_pre_topc @ X24 @ X23)
% 0.47/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.47/0.70          | ~ (l1_pre_topc @ X23)
% 0.47/0.70          | ~ (v2_pre_topc @ X23))),
% 0.47/0.70      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.47/0.70  thf('58', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v3_pre_topc @ 
% 0.47/0.70             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.70  thf('59', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(t29_tops_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( v4_pre_topc @ B @ A ) <=>
% 0.47/0.70             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.47/0.70  thf('60', plain,
% 0.47/0.70      (![X13 : $i, X14 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.70          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.47/0.70          | (v4_pre_topc @ X13 @ X14)
% 0.47/0.70          | ~ (l1_pre_topc @ X14))),
% 0.47/0.70      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.47/0.70  thf('61', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v3_pre_topc @ 
% 0.47/0.70               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.70  thf('62', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_tdlat_3 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['58', '61'])).
% 0.47/0.70  thf('63', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.70  thf('64', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(t52_pre_topc, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.47/0.70             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.47/0.70               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('65', plain,
% 0.47/0.70      (![X11 : $i, X12 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.47/0.70          | ~ (v4_pre_topc @ X11 @ X12)
% 0.47/0.70          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.47/0.70          | ~ (l1_pre_topc @ X12))),
% 0.47/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.47/0.70  thf('66', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.70  thf('67', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_tdlat_3 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['63', '66'])).
% 0.47/0.70  thf('68', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.47/0.70  thf('69', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(d2_tops_3, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( v1_tops_1 @ B @ A ) <=>
% 0.47/0.70             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('70', plain,
% 0.47/0.70      (![X16 : $i, X17 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.70          | ((k2_pre_topc @ X17 @ X16) != (u1_struct_0 @ X17))
% 0.47/0.70          | (v1_tops_1 @ X16 @ X17)
% 0.47/0.70          | ~ (l1_pre_topc @ X17))),
% 0.47/0.70      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.47/0.70  thf('71', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.70  thf('72', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['68', '71'])).
% 0.47/0.70  thf('73', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['72'])).
% 0.47/0.70  thf('74', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.70  thf(t48_tex_2, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.47/0.70             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.47/0.70  thf('75', plain,
% 0.47/0.70      (![X27 : $i, X28 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.47/0.70          | (v3_tex_2 @ X27 @ X28)
% 0.47/0.70          | ~ (v2_tex_2 @ X27 @ X28)
% 0.47/0.70          | ~ (v1_tops_1 @ X27 @ X28)
% 0.47/0.70          | ~ (l1_pre_topc @ X28)
% 0.47/0.70          | ~ (v2_pre_topc @ X28)
% 0.47/0.70          | (v2_struct_0 @ X28))),
% 0.47/0.70      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.47/0.70  thf('76', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.70  thf('77', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_tdlat_3 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['73', '76'])).
% 0.47/0.70  thf('78', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['77'])).
% 0.47/0.70  thf('79', plain,
% 0.47/0.70      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.47/0.70        | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.47/0.70        | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['53', '78'])).
% 0.47/0.70  thf('80', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('81', plain,
% 0.47/0.70      (![X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.70          | (v2_tex_2 @ X25 @ X26)
% 0.47/0.70          | ~ (l1_pre_topc @ X26)
% 0.47/0.70          | ~ (v1_tdlat_3 @ X26)
% 0.47/0.70          | ~ (v2_pre_topc @ X26)
% 0.47/0.70          | (v2_struct_0 @ X26))),
% 0.47/0.70      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.47/0.70  thf('82', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_A)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70        | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.70  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('84', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('86', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.47/0.70  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('88', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.47/0.70      inference('clc', [status(thm)], ['86', '87'])).
% 0.47/0.70  thf('89', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('92', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['6', '52'])).
% 0.47/0.70  thf('93', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['79', '88', '89', '90', '91', '92'])).
% 0.47/0.70  thf('94', plain,
% 0.47/0.70      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['45'])).
% 0.47/0.70  thf('95', plain,
% 0.47/0.70      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.47/0.70       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.70      inference('split', [status(esa)], ['45'])).
% 0.47/0.70  thf('96', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.70      inference('sat_resolution*', [status(thm)], ['7', '51', '95'])).
% 0.47/0.70  thf('97', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.47/0.70      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 0.47/0.70  thf('98', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('clc', [status(thm)], ['93', '97'])).
% 0.47/0.70  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
