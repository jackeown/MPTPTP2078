%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTJa4CLPfn

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 363 expanded)
%              Number of leaves         :   36 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  991 (3834 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
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
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('41',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ X11 @ X11 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','44'])).

thf('46',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_tdlat_3 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) @ X15 )
      | ( v4_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X12 )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( u1_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_tex_2 @ X28 @ X29 )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','45'])).

thf('86',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('88',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('89',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','44','88'])).

thf('90',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['87','89'])).

thf('91',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['86','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTJa4CLPfn
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 323 iterations in 0.200s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.65  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.46/0.65  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.46/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.65  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(t49_tex_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.46/0.65         ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v3_tex_2 @ B @ A ) <=>
% 0.46/0.65             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.65            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65              ( ( v3_tex_2 @ B @ A ) <=>
% 0.46/0.65                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.46/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d7_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         (((X20) = (X19))
% 0.46/0.65          | (v1_subset_1 @ X20 @ X19)
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.46/0.65       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf(dt_k2_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.65  thf('9', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.65  thf('10', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(t43_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.46/0.65         ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.65          | (v2_tex_2 @ X26 @ X27)
% 0.46/0.65          | ~ (l1_pre_topc @ X27)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X27)
% 0.46/0.65          | ~ (v2_pre_topc @ X27)
% 0.46/0.65          | (v2_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d7_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v3_tex_2 @ B @ A ) <=>
% 0.46/0.65             ( ( v2_tex_2 @ B @ A ) & 
% 0.46/0.65               ( ![C:$i]:
% 0.46/0.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.65                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.65          | ~ (v3_tex_2 @ X21 @ X22)
% 0.46/0.65          | ~ (v2_tex_2 @ X23 @ X22)
% 0.46/0.65          | ~ (r1_tarski @ X21 @ X23)
% 0.46/0.65          | ((X21) = (X23))
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.65          | ~ (l1_pre_topc @ X22))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | ((sk_B_1) = (X0))
% 0.46/0.65          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.65          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | ((sk_B_1) = (X0))
% 0.46/0.65          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.65          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.65           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65           | ((sk_B_1) = (X0))
% 0.46/0.65           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.46/0.65         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '20'])).
% 0.46/0.65  thf(d3_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(l3_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X8 @ X9)
% 0.46/0.65          | (r2_hidden @ X8 @ X10)
% 0.46/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.65      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.46/0.65         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.65         | ~ (v1_tdlat_3 @ sk_A)
% 0.46/0.65         | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '30'])).
% 0.46/0.65  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.46/0.65  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.46/0.65         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.46/0.65             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['37', '39'])).
% 0.46/0.65  thf(fc14_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.46/0.65  thf('41', plain, (![X11 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X11) @ X11)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.46/0.65  thf('42', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.65  thf('43', plain, (![X11 : $i]: ~ (v1_subset_1 @ X11 @ X11)),
% 0.46/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.46/0.65       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.65  thf('45', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['7', '44'])).
% 0.46/0.65  thf('46', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.46/0.65  thf('47', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(dt_k3_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.46/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf(t17_tdlat_3, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ( v1_tdlat_3 @ A ) <=>
% 0.46/0.65         ( ![B:$i]:
% 0.46/0.65           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (v1_tdlat_3 @ X24)
% 0.46/0.65          | (v3_pre_topc @ X25 @ X24)
% 0.46/0.65          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.65          | ~ (l1_pre_topc @ X24)
% 0.46/0.65          | ~ (v2_pre_topc @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v3_pre_topc @ 
% 0.46/0.65             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('52', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(t29_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.65             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.65          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14) @ X15)
% 0.46/0.65          | (v4_pre_topc @ X14 @ X15)
% 0.46/0.65          | ~ (l1_pre_topc @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v3_pre_topc @ 
% 0.46/0.65               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.65  thf('57', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(t52_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.65             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.65               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.65          | ~ (v4_pre_topc @ X12 @ X13)
% 0.46/0.65          | ((k2_pre_topc @ X13 @ X12) = (X12))
% 0.46/0.65          | ~ (l1_pre_topc @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('62', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(d2_tops_3, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v1_tops_1 @ B @ A ) <=>
% 0.46/0.65             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.65          | ((k2_pre_topc @ X18 @ X17) != (u1_struct_0 @ X18))
% 0.46/0.65          | (v1_tops_1 @ X17 @ X18)
% 0.46/0.65          | ~ (l1_pre_topc @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['61', '64'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.65  thf('67', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(t48_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.46/0.65             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.65          | (v3_tex_2 @ X28 @ X29)
% 0.46/0.65          | ~ (v2_tex_2 @ X28 @ X29)
% 0.46/0.65          | ~ (v1_tops_1 @ X28 @ X29)
% 0.46/0.65          | ~ (l1_pre_topc @ X29)
% 0.46/0.65          | ~ (v2_pre_topc @ X29)
% 0.46/0.65          | (v2_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_tdlat_3 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['66', '69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['46', '71'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.65          | (v2_tex_2 @ X26 @ X27)
% 0.46/0.65          | ~ (l1_pre_topc @ X27)
% 0.46/0.65          | ~ (v1_tdlat_3 @ X27)
% 0.46/0.65          | ~ (v2_pre_topc @ X27)
% 0.46/0.65          | (v2_struct_0 @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (v1_tdlat_3 @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.65  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('77', plain, ((v1_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('79', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.46/0.65  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('81', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain, ((v1_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('85', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['6', '45'])).
% 0.46/0.65  thf('86', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '81', '82', '83', '84', '85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['38'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.46/0.65       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['38'])).
% 0.46/0.65  thf('89', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['7', '44', '88'])).
% 0.46/0.65  thf('90', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.46/0.65  thf('91', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('clc', [status(thm)], ['86', '90'])).
% 0.46/0.65  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
