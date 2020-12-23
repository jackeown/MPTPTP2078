%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OETTEJ0t8c

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 263 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  943 (2669 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X23 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('48',plain,(
    ! [X13: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X12: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( u1_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ~ ( v1_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('77',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75','78'])).

thf('80',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('81',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('82',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','44','81'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OETTEJ0t8c
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 287 iterations in 0.162s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.42/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.63  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.42/0.63  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.42/0.63  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.42/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.63  thf(t49_tex_2, conjecture,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.42/0.63         ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( v3_tex_2 @ B @ A ) <=>
% 0.42/0.63             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i]:
% 0.42/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.63            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63          ( ![B:$i]:
% 0.42/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63              ( ( v3_tex_2 @ B @ A ) <=>
% 0.42/0.63                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.42/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('1', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(d7_subset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      (![X19 : $i, X20 : $i]:
% 0.42/0.63         (((X20) = (X19))
% 0.42/0.63          | (v1_subset_1 @ X20 @ X19)
% 0.42/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.42/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.42/0.63        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.42/0.63        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.42/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('split', [status(esa)], ['4'])).
% 0.42/0.63  thf('6', plain,
% 0.42/0.63      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.42/0.63         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['3', '5'])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.42/0.63       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.42/0.63      inference('split', [status(esa)], ['4'])).
% 0.42/0.63  thf(dt_k2_subset_1, axiom,
% 0.42/0.63    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.63  thf('8', plain,
% 0.42/0.63      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.63  thf('9', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.42/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.63  thf('10', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.42/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf(t43_tex_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.42/0.63         ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      (![X24 : $i, X25 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.42/0.63          | (v2_tex_2 @ X24 @ X25)
% 0.42/0.63          | ~ (l1_pre_topc @ X25)
% 0.42/0.63          | ~ (v1_tdlat_3 @ X25)
% 0.42/0.63          | ~ (v2_pre_topc @ X25)
% 0.42/0.63          | (v2_struct_0 @ X25))),
% 0.42/0.63      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (v1_tdlat_3 @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.63  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.42/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf('14', plain,
% 0.42/0.63      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['4'])).
% 0.42/0.63  thf('15', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(d7_tex_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( v3_tex_2 @ B @ A ) <=>
% 0.42/0.63             ( ( v2_tex_2 @ B @ A ) & 
% 0.42/0.63               ( ![C:$i]:
% 0.42/0.63                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.63                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('16', plain,
% 0.42/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.42/0.63          | ~ (v3_tex_2 @ X21 @ X22)
% 0.42/0.63          | ~ (v2_tex_2 @ X23 @ X22)
% 0.42/0.63          | ~ (r1_tarski @ X21 @ X23)
% 0.42/0.63          | ((X21) = (X23))
% 0.42/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.42/0.63          | ~ (l1_pre_topc @ X22))),
% 0.42/0.63      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.42/0.63  thf('17', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ sk_A)
% 0.42/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.63          | ((sk_B) = (X0))
% 0.42/0.63          | ~ (r1_tarski @ sk_B @ X0)
% 0.42/0.63          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.63          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.63          | ((sk_B) = (X0))
% 0.42/0.63          | ~ (r1_tarski @ sk_B @ X0)
% 0.42/0.63          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.63          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      ((![X0 : $i]:
% 0.42/0.63          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.63           | ~ (r1_tarski @ sk_B @ X0)
% 0.42/0.63           | ((sk_B) = (X0))
% 0.42/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.42/0.63         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.63         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.63         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['13', '20'])).
% 0.47/0.63  thf(d3_tarski, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X1 : $i, X3 : $i]:
% 0.47/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(l3_subset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X6 @ X7)
% 0.47/0.63          | (r2_hidden @ X6 @ X8)
% 0.47/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.47/0.63  thf('25', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.47/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_B @ X0)
% 0.47/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X1 : $i, X3 : $i]:
% 0.47/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.63         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.63         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['21', '29'])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['12', '30'])).
% 0.47/0.63  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.47/0.63  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('clc', [status(thm)], ['35', '36'])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.47/0.63         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('split', [status(esa)], ['38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (((v1_subset_1 @ sk_B @ sk_B))
% 0.47/0.63         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.47/0.63             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['37', '39'])).
% 0.47/0.63  thf(fc14_subset_1, axiom,
% 0.47/0.63    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.47/0.63  thf('41', plain, (![X9 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X9) @ X9)),
% 0.47/0.63      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.47/0.63  thf('42', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.47/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.63  thf('43', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 0.47/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.47/0.63       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['40', '43'])).
% 0.47/0.63  thf('45', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['7', '44'])).
% 0.47/0.63  thf('46', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.63  thf(fc4_pre_topc, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X13 : $i]:
% 0.47/0.63         ((v4_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.47/0.63          | ~ (l1_pre_topc @ X13)
% 0.47/0.63          | ~ (v2_pre_topc @ X13))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.47/0.63  thf(dt_k2_struct_0, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_struct_0 @ A ) =>
% 0.47/0.63       ( m1_subset_1 @
% 0.47/0.63         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (![X10 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (k2_struct_0 @ X10) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.47/0.63          | ~ (l1_struct_0 @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      (![X19 : $i, X20 : $i]:
% 0.47/0.63         (((X20) = (X19))
% 0.47/0.63          | (v1_subset_1 @ X20 @ X19)
% 0.47/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_subset_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.47/0.63          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.63  thf(fc12_struct_0, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_struct_0 @ A ) =>
% 0.47/0.63       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      (![X12 : $i]:
% 0.47/0.63         (~ (v1_subset_1 @ (k2_struct_0 @ X12) @ (u1_struct_0 @ X12))
% 0.47/0.63          | ~ (l1_struct_0 @ X12))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.47/0.63  thf('53', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.47/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.47/0.63  thf('54', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.63  thf(t52_pre_topc, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.47/0.63             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.47/0.63               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (![X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.63          | ~ (v4_pre_topc @ X14 @ X15)
% 0.47/0.63          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.47/0.63          | ~ (l1_pre_topc @ X15))),
% 0.47/0.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.47/0.63  thf('56', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.63          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.63  thf('57', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['53', '56'])).
% 0.47/0.63  thf('58', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.63          | ~ (l1_struct_0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['48', '57'])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_struct_0 @ X0)
% 0.47/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['58'])).
% 0.47/0.63  thf('60', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.63  thf(d2_tops_3, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( v1_tops_1 @ B @ A ) <=>
% 0.47/0.63             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('61', plain,
% 0.47/0.63      (![X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.63          | ((k2_pre_topc @ X18 @ X17) != (u1_struct_0 @ X18))
% 0.47/0.63          | (v1_tops_1 @ X17 @ X18)
% 0.47/0.63          | ~ (l1_pre_topc @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.47/0.63  thf('62', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.63  thf('63', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['59', '62'])).
% 0.47/0.63  thf('64', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['63'])).
% 0.47/0.63  thf('65', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.63  thf(t48_tex_2, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.47/0.63             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.47/0.63  thf('66', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.47/0.63          | (v3_tex_2 @ X26 @ X27)
% 0.47/0.63          | ~ (v2_tex_2 @ X26 @ X27)
% 0.47/0.63          | ~ (v1_tops_1 @ X26 @ X27)
% 0.47/0.63          | ~ (l1_pre_topc @ X27)
% 0.47/0.63          | ~ (v2_pre_topc @ X27)
% 0.47/0.63          | (v2_struct_0 @ X27))),
% 0.47/0.63      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['64', '67'])).
% 0.47/0.63  thf('69', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['68'])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['47', '69'])).
% 0.47/0.63  thf('71', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['70'])).
% 0.47/0.63  thf('72', plain,
% 0.47/0.63      (((v3_tex_2 @ sk_B @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['46', '71'])).
% 0.47/0.63  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('74', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(dt_l1_pre_topc, axiom,
% 0.47/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.63  thf('79', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['72', '73', '74', '75', '78'])).
% 0.47/0.63  thf('80', plain,
% 0.47/0.63      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.47/0.63      inference('split', [status(esa)], ['38'])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.47/0.63       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('split', [status(esa)], ['38'])).
% 0.47/0.63  thf('82', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['7', '44', '81'])).
% 0.47/0.63  thf('83', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.47/0.63  thf('84', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('clc', [status(thm)], ['79', '83'])).
% 0.47/0.63  thf('85', plain, ($false), inference('demod', [status(thm)], ['0', '84'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
