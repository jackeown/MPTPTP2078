%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sp2QfSEwNt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:16 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 340 expanded)
%              Number of leaves         :   33 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  936 (3642 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('36',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','39'])).

thf('41',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_tdlat_3 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v4_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X8 @ X9 )
      | ( ( k2_pre_topc @ X9 @ X8 )
        = X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ X13 )
       != ( u1_struct_0 @ X14 ) )
      | ( v1_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','40'])).

thf('81',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','76','77','78','79','80'])).

thf('82',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('83',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('84',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','39','83'])).

thf('85',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['81','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sp2QfSEwNt
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 323 iterations in 0.351s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.81  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.58/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.81  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.81  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.58/0.81  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.58/0.81  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.58/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.81  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.58/0.81  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.58/0.81  thf(t49_tex_2, conjecture,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.58/0.81         ( l1_pre_topc @ A ) ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( v3_tex_2 @ B @ A ) <=>
% 0.58/0.81             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i]:
% 0.58/0.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.81            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.81          ( ![B:$i]:
% 0.58/0.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81              ( ( v3_tex_2 @ B @ A ) <=>
% 0.58/0.81                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.58/0.81  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('1', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(d7_subset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.81       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i]:
% 0.58/0.81         (((X16) = (X15))
% 0.58/0.81          | (v1_subset_1 @ X16 @ X15)
% 0.58/0.81          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.58/0.81      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.81         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.81      inference('split', [status(esa)], ['4'])).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.58/0.81         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['3', '5'])).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.58/0.81       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('split', [status(esa)], ['4'])).
% 0.58/0.81  thf(dt_k2_subset_1, axiom,
% 0.58/0.81    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.58/0.81  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.81  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.81  thf('10', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(t43_tex_2, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.58/0.81         ( l1_pre_topc @ A ) ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X22 : $i, X23 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.58/0.81          | (v2_tex_2 @ X22 @ X23)
% 0.58/0.81          | ~ (l1_pre_topc @ X23)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X23)
% 0.58/0.81          | ~ (v2_pre_topc @ X23)
% 0.58/0.81          | (v2_struct_0 @ X23))),
% 0.58/0.81      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.81  thf('13', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('split', [status(esa)], ['4'])).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(d7_tex_2, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( l1_pre_topc @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( v3_tex_2 @ B @ A ) <=>
% 0.58/0.81             ( ( v2_tex_2 @ B @ A ) & 
% 0.58/0.81               ( ![C:$i]:
% 0.58/0.81                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.81                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.58/0.81          | ~ (v3_tex_2 @ X17 @ X18)
% 0.58/0.81          | ~ (v2_tex_2 @ X19 @ X18)
% 0.58/0.81          | ~ (r1_tarski @ X17 @ X19)
% 0.58/0.81          | ((X17) = (X19))
% 0.58/0.81          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.58/0.81          | ~ (l1_pre_topc @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (l1_pre_topc @ sk_A)
% 0.58/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.81          | ((sk_B_1) = (X0))
% 0.58/0.81          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.58/0.81          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.58/0.81          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.81  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.81          | ((sk_B_1) = (X0))
% 0.58/0.81          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.58/0.81          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.58/0.81          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.81  thf('20', plain,
% 0.58/0.81      ((![X0 : $i]:
% 0.58/0.81          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.58/0.81           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.58/0.81           | ((sk_B_1) = (X0))
% 0.58/0.81           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['14', '19'])).
% 0.58/0.81  thf('21', plain,
% 0.58/0.81      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.58/0.81         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.81         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['13', '20'])).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t3_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (![X5 : $i, X6 : $i]:
% 0.58/0.81         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('24', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.81  thf('25', plain,
% 0.58/0.81      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.58/0.81         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['21', '24'])).
% 0.58/0.81  thf('26', plain,
% 0.58/0.81      (((~ (l1_pre_topc @ sk_A)
% 0.58/0.81         | ~ (v1_tdlat_3 @ sk_A)
% 0.58/0.81         | ~ (v2_pre_topc @ sk_A)
% 0.58/0.81         | (v2_struct_0 @ sk_A)
% 0.58/0.81         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['12', '25'])).
% 0.58/0.81  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.58/0.81  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('clc', [status(thm)], ['30', '31'])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.81        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.81         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.81      inference('split', [status(esa)], ['33'])).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.58/0.81         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.58/0.81             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.81      inference('sup+', [status(thm)], ['32', '34'])).
% 0.58/0.81  thf(fc14_subset_1, axiom,
% 0.58/0.81    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.58/0.81  thf('36', plain, (![X4 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X4) @ X4)),
% 0.58/0.81      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.58/0.81  thf('37', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.81  thf('38', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 0.58/0.81      inference('demod', [status(thm)], ['36', '37'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.58/0.81       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['35', '38'])).
% 0.58/0.81  thf('40', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('sat_resolution*', [status(thm)], ['7', '39'])).
% 0.58/0.81  thf('41', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['6', '40'])).
% 0.58/0.81  thf('42', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(dt_k3_subset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.81       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i]:
% 0.58/0.81         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.58/0.81          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.81  thf(t17_tdlat_3, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.81       ( ( v1_tdlat_3 @ A ) <=>
% 0.58/0.81         ( ![B:$i]:
% 0.58/0.81           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      (![X20 : $i, X21 : $i]:
% 0.58/0.81         (~ (v1_tdlat_3 @ X20)
% 0.58/0.81          | (v3_pre_topc @ X21 @ X20)
% 0.58/0.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.58/0.81          | ~ (l1_pre_topc @ X20)
% 0.58/0.81          | ~ (v2_pre_topc @ X20))),
% 0.58/0.81      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v3_pre_topc @ 
% 0.58/0.81             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.81  thf('47', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(t29_tops_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( l1_pre_topc @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.81             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (![X10 : $i, X11 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.58/0.81          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.58/0.81          | (v4_pre_topc @ X10 @ X11)
% 0.58/0.81          | ~ (l1_pre_topc @ X11))),
% 0.58/0.81      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v3_pre_topc @ 
% 0.58/0.81               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_tdlat_3 @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['46', '49'])).
% 0.58/0.81  thf('51', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['50'])).
% 0.58/0.81  thf('52', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(t52_pre_topc, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( l1_pre_topc @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.58/0.81             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.58/0.81               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.58/0.81          | ~ (v4_pre_topc @ X8 @ X9)
% 0.58/0.81          | ((k2_pre_topc @ X9 @ X8) = (X8))
% 0.58/0.81          | ~ (l1_pre_topc @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (l1_pre_topc @ X0)
% 0.58/0.81          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.58/0.81          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.81  thf('55', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_tdlat_3 @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.58/0.81          | ~ (l1_pre_topc @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['51', '54'])).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.81  thf('57', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(d2_tops_3, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( l1_pre_topc @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( v1_tops_1 @ B @ A ) <=>
% 0.58/0.81             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.58/0.81  thf('58', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.58/0.81          | ((k2_pre_topc @ X14 @ X13) != (u1_struct_0 @ X14))
% 0.58/0.81          | (v1_tops_1 @ X13 @ X14)
% 0.58/0.81          | ~ (l1_pre_topc @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (l1_pre_topc @ X0)
% 0.58/0.81          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.81  thf('60', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['56', '59'])).
% 0.58/0.81  thf('61', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['60'])).
% 0.58/0.81  thf('62', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.58/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf(t48_tex_2, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.81           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.58/0.81             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.58/0.81  thf('63', plain,
% 0.58/0.81      (![X24 : $i, X25 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.58/0.81          | (v3_tex_2 @ X24 @ X25)
% 0.58/0.81          | ~ (v2_tex_2 @ X24 @ X25)
% 0.58/0.81          | ~ (v1_tops_1 @ X24 @ X25)
% 0.58/0.81          | ~ (l1_pre_topc @ X25)
% 0.58/0.81          | ~ (v2_pre_topc @ X25)
% 0.58/0.81          | (v2_struct_0 @ X25))),
% 0.58/0.81      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_tdlat_3 @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | (v2_struct_0 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['61', '64'])).
% 0.58/0.81  thf('66', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v2_struct_0 @ X0)
% 0.58/0.81          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.58/0.81          | ~ (v2_pre_topc @ X0)
% 0.58/0.81          | ~ (l1_pre_topc @ X0)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['65'])).
% 0.58/0.81  thf('67', plain,
% 0.58/0.81      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.81        | ~ (v1_tdlat_3 @ sk_A)
% 0.58/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.81        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['41', '66'])).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('69', plain,
% 0.58/0.81      (![X22 : $i, X23 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.58/0.81          | (v2_tex_2 @ X22 @ X23)
% 0.58/0.81          | ~ (l1_pre_topc @ X23)
% 0.58/0.81          | ~ (v1_tdlat_3 @ X23)
% 0.58/0.81          | ~ (v2_pre_topc @ X23)
% 0.58/0.81          | (v2_struct_0 @ X23))),
% 0.58/0.81      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.58/0.81  thf('70', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A)
% 0.58/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.81        | ~ (v1_tdlat_3 @ sk_A)
% 0.58/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.81  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('72', plain, ((v1_tdlat_3 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('74', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.58/0.81  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('76', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.81      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.81  thf('77', plain, ((v1_tdlat_3 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('80', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['6', '40'])).
% 0.58/0.81  thf('81', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['67', '76', '77', '78', '79', '80'])).
% 0.58/0.81  thf('82', plain,
% 0.58/0.81      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.81      inference('split', [status(esa)], ['33'])).
% 0.58/0.81  thf('83', plain,
% 0.58/0.81      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.58/0.81       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.81      inference('split', [status(esa)], ['33'])).
% 0.58/0.81  thf('84', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.81      inference('sat_resolution*', [status(thm)], ['7', '39', '83'])).
% 0.58/0.81  thf('85', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.58/0.81  thf('86', plain, ((v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('clc', [status(thm)], ['81', '85'])).
% 0.58/0.81  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
