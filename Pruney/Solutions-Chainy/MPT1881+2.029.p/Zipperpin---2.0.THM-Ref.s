%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GmKhmesW5z

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 589 expanded)
%              Number of leaves         :   36 ( 180 expanded)
%              Depth                    :   18
%              Number of atoms          :  956 (6467 expanded)
%              Number of equality atoms :   41 ( 139 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('41',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ X9 @ X9 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','44'])).

thf('46',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('52',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('56',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('58',plain,
    ( ( ( sk_B
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('63',plain,(
    ! [X12: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('64',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('69',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','67','68','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( k2_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( sk_B
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( sk_B
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('79',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','44'])).

thf('82',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('84',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','82','83','84','93','94','95'])).

thf('97',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('98',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('99',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','44','98'])).

thf('100',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['97','99'])).

thf('101',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['96','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GmKhmesW5z
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 209 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(t49_tex_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.53             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53              ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.53                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d7_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (((X19) = (X18))
% 0.21/0.53          | (v1_subset_1 @ X19 @ X18)
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.53       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf(dt_k2_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('9', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('10', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t43_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.53          | (v2_tex_2 @ X23 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X24)
% 0.21/0.53          | ~ (v2_pre_topc @ X24)
% 0.21/0.53          | (v2_struct_0 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['4'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d7_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.53             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.53               ( ![C:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (v3_tex_2 @ X20 @ X21)
% 0.21/0.53          | ~ (v2_tex_2 @ X22 @ X21)
% 0.21/0.53          | ~ (r1_tarski @ X20 @ X22)
% 0.21/0.53          | ((X20) = (X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | ~ (l1_pre_topc @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ((sk_B) = (X0))
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.53          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ((sk_B) = (X0))
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.53          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.53           | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.53           | ((sk_B) = (X0))
% 0.21/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '20'])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l3_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.53          | (r2_hidden @ X6 @ X8)
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_B @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_A)
% 0.21/0.53         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '30'])).
% 0.21/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.53  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ sk_B))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.21/0.53             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['37', '39'])).
% 0.21/0.53  thf(fc14_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.53  thf('41', plain, (![X9 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X9) @ X9)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.53  thf('42', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('43', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.53       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.53  thf('45', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '44'])).
% 0.21/0.53  thf('46', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.21/0.53  thf('47', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t48_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.53             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.53          | (v3_tex_2 @ X25 @ X26)
% 0.21/0.53          | ~ (v2_tex_2 @ X25 @ X26)
% 0.21/0.53          | ~ (v1_tops_1 @ X25 @ X26)
% 0.21/0.53          | ~ (l1_pre_topc @ X26)
% 0.21/0.53          | ~ (v2_pre_topc @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((~ (v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.53        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('52', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t52_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.53          | ~ (v4_pre_topc @ X13 @ X14)
% 0.21/0.53          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.21/0.53          | ~ (l1_pre_topc @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.53         | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.53  thf(d3_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X10 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (((((sk_B) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      ((((sk_B) = (k2_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '61'])).
% 0.21/0.53  thf(fc4_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         ((v4_pre_topc @ (k2_struct_0 @ X12) @ X12)
% 0.21/0.53          | ~ (l1_pre_topc @ X12)
% 0.21/0.53          | ~ (v2_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v4_pre_topc @ sk_B @ sk_A))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.53  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '67', '68', '69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d3_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.53             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ((k2_pre_topc @ X16 @ X15) != (k2_struct_0 @ X16))
% 0.21/0.53          | (v1_tops_1 @ X15 @ X16)
% 0.21/0.53          | ~ (l1_pre_topc @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.53        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.53  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (((v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.53        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      (((((sk_B) != (k2_struct_0 @ sk_A)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['71', '76'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      ((((sk_B) = (k2_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '61'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (((((sk_B) != (sk_B)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      (((v1_tops_1 @ sk_B @ sk_A))
% 0.21/0.53         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['79'])).
% 0.21/0.53  thf('81', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '44'])).
% 0.21/0.53  thf('82', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.21/0.53  thf('83', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.21/0.53  thf('84', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.53          | (v2_tex_2 @ X23 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X24)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X24)
% 0.21/0.53          | ~ (v2_pre_topc @ X24)
% 0.21/0.53          | (v2_struct_0 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.53  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('89', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.21/0.53  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.53  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('96', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['50', '82', '83', '84', '93', '94', '95'])).
% 0.21/0.53  thf('97', plain,
% 0.21/0.53      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['38'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.53       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['38'])).
% 0.21/0.53  thf('99', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '44', '98'])).
% 0.21/0.53  thf('100', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['97', '99'])).
% 0.21/0.53  thf('101', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['96', '100'])).
% 0.21/0.53  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
