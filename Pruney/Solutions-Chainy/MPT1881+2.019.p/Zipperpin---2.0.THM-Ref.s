%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4L06hfxXAL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:14 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 916 expanded)
%              Number of leaves         :   41 ( 274 expanded)
%              Depth                    :   20
%              Number of atoms          : 1253 (9980 expanded)
%              Number of equality atoms :   44 ( 208 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 = X23 )
      | ( v1_subset_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
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

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,
    ( ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 = X23 )
      | ( v1_subset_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('14',plain,
    ( ( ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
      | ( ( k2_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('17',plain,
    ( ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','19'])).

thf('21',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v2_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X27 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( X25 = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_B_1 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','43'])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['51','53'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('55',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('57',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ X12 @ X12 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','58'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['20','59'])).

thf('61',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('62',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v3_tex_2 @ X32 @ X33 )
      | ~ ( v2_tex_2 @ X32 @ X33 )
      | ~ ( v1_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['20','59'])).

thf('66',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['20','59'])).

thf('67',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('69',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','58'])).

thf('75',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('81',plain,
    ( ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','77','78','79','80'])).

thf('82',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('83',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('84',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
       != ( u1_struct_0 @ X22 ) )
      | ( v1_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('91',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','19'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_pre_topc @ ( k7_subset_1 @ sk_B_1 @ sk_B_1 @ X0 ) @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('102',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_tdlat_3 @ X28 )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k7_subset_1 @ sk_B_1 @ sk_B_1 @ X0 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','108'])).

thf('110',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('112',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','58'])).

thf('118',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','118'])).

thf('120',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','58'])).

thf('122',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','122'])).

thf('124',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['52'])).

thf('125',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('126',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['21','58','125'])).

thf('127',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['124','126'])).

thf('128',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['123','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4L06hfxXAL
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 404 iterations in 0.209s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.47/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.47/0.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.47/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.66  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.47/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.66  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.47/0.66  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.66  thf(t49_tex_2, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.47/0.66         ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.66             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.66            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66              ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.66                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.47/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d7_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         (((X24) = (X23))
% 0.47/0.66          | (v1_subset_1 @ X24 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['4'])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf(dt_k2_struct_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_struct_0 @ A ) =>
% 0.47/0.66       ( m1_subset_1 @
% 0.47/0.66         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X15 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k2_struct_0 @ X15) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | ~ (l1_struct_0 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.66         | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_l1_pre_topc, axiom,
% 0.47/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.66  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         (((X24) = (X23))
% 0.47/0.66          | (v1_subset_1 @ X24 @ X23)
% 0.47/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      ((((v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.47/0.66         | ((k2_struct_0 @ sk_A) = (sk_B_1))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf(fc12_struct_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_struct_0 @ A ) =>
% 0.47/0.66       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X17 : $i]:
% 0.47/0.66         (~ (v1_subset_1 @ (k2_struct_0 @ X17) @ (u1_struct_0 @ X17))
% 0.47/0.66          | ~ (l1_struct_0 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.47/0.66         | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (sk_B_1)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('clc', [status(thm)], ['14', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.47/0.66       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('split', [status(esa)], ['4'])).
% 0.47/0.66  thf(dt_k2_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.47/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.66  thf('23', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('24', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf(t43_tex_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.47/0.66         ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X30 : $i, X31 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.47/0.66          | (v2_tex_2 @ X30 @ X31)
% 0.47/0.66          | ~ (l1_pre_topc @ X31)
% 0.47/0.66          | ~ (v1_tdlat_3 @ X31)
% 0.47/0.66          | ~ (v2_pre_topc @ X31)
% 0.47/0.66          | (v2_struct_0 @ X31))),
% 0.47/0.66      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['4'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d7_tex_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.66             ( ( v2_tex_2 @ B @ A ) & 
% 0.47/0.66               ( ![C:$i]:
% 0.47/0.66                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.66                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.66          | ~ (v3_tex_2 @ X25 @ X26)
% 0.47/0.66          | ~ (v2_tex_2 @ X27 @ X26)
% 0.47/0.66          | ~ (r1_tarski @ X25 @ X27)
% 0.47/0.66          | ((X25) = (X27))
% 0.47/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.66          | ~ (l1_pre_topc @ X26))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | ((sk_B_1) = (X0))
% 0.47/0.66          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.66          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | ((sk_B_1) = (X0))
% 0.47/0.66          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.66          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.47/0.66           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | ((sk_B_1) = (X0))
% 0.47/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.47/0.66         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '34'])).
% 0.47/0.66  thf(d3_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(l3_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X9 @ X10)
% 0.47/0.66          | (r2_hidden @ X9 @ X11)
% 0.47/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['36', '39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.47/0.66         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['35', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66         | (v2_struct_0 @ sk_A)
% 0.47/0.66         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '44'])).
% 0.47/0.66  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('47', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.47/0.66  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['49', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.47/0.66         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.47/0.66             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['51', '53'])).
% 0.47/0.66  thf(fc14_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.47/0.66  thf('55', plain, (![X12 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X12) @ X12)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.47/0.66  thf('56', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('57', plain, (![X12 : $i]: ~ (v1_subset_1 @ X12 @ X12)),
% 0.47/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.47/0.66       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['54', '57'])).
% 0.47/0.66  thf('59', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['21', '58'])).
% 0.47/0.66  thf('60', plain, (((k2_struct_0 @ sk_A) = (sk_B_1))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['20', '59'])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (![X15 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k2_struct_0 @ X15) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.66          | ~ (l1_struct_0 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.66  thf(t48_tex_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.47/0.66             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      (![X32 : $i, X33 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.47/0.66          | (v3_tex_2 @ X32 @ X33)
% 0.47/0.66          | ~ (v2_tex_2 @ X32 @ X33)
% 0.47/0.66          | ~ (v1_tops_1 @ X32 @ X33)
% 0.47/0.66          | ~ (l1_pre_topc @ X33)
% 0.47/0.66          | ~ (v2_pre_topc @ X33)
% 0.47/0.66          | (v2_struct_0 @ X33))),
% 0.47/0.66      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.66          | ~ (v2_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.66          | (v3_tex_2 @ (k2_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      ((~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.47/0.66        | (v3_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.47/0.66        | ~ (v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.47/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['60', '63'])).
% 0.47/0.66  thf('65', plain, (((k2_struct_0 @ sk_A) = (sk_B_1))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['20', '59'])).
% 0.47/0.66  thf('66', plain, (((k2_struct_0 @ sk_A) = (sk_B_1))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['20', '59'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X0)
% 0.47/0.66          | ~ (v2_pre_topc @ X0)
% 0.47/0.66          | ~ (v1_tdlat_3 @ X0)
% 0.47/0.66          | ~ (l1_pre_topc @ X0)
% 0.47/0.66          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | ~ (v1_tdlat_3 @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('71', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.47/0.66  thf('74', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['21', '58'])).
% 0.47/0.66  thf('75', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.47/0.66  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('77', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['75', '76'])).
% 0.47/0.66  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      ((~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.47/0.66        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)],
% 0.47/0.66                ['64', '65', '66', '77', '78', '79', '80'])).
% 0.47/0.66  thf('82', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf(d2_tops_3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( v1_tops_1 @ B @ A ) <=>
% 0.47/0.66             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('84', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.66          | ((k2_pre_topc @ X22 @ X21) != (u1_struct_0 @ X22))
% 0.47/0.66          | (v1_tops_1 @ X21 @ X22)
% 0.47/0.66          | ~ (l1_pre_topc @ X22))),
% 0.47/0.66      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.66           | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66           | (v1_tops_1 @ X0 @ sk_A)
% 0.47/0.66           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['83', '84'])).
% 0.47/0.66  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('87', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.66           | (v1_tops_1 @ X0 @ sk_A)
% 0.47/0.66           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.47/0.66  thf('89', plain,
% 0.47/0.66      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.47/0.66         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['82', '88'])).
% 0.47/0.66  thf('90', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf(d6_pre_topc, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.47/0.66             ( v3_pre_topc @
% 0.47/0.66               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.47/0.66               A ) ) ) ) ))).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (![X13 : $i, X14 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.66          | ~ (v3_pre_topc @ 
% 0.47/0.66               (k7_subset_1 @ (u1_struct_0 @ X14) @ (k2_struct_0 @ X14) @ X13) @ 
% 0.47/0.66               X14)
% 0.47/0.66          | (v4_pre_topc @ X13 @ X14)
% 0.47/0.66          | ~ (l1_pre_topc @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (v3_pre_topc @ 
% 0.47/0.66              (k7_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_A)
% 0.47/0.66           | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66           | (v4_pre_topc @ X0 @ sk_A)
% 0.47/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      ((((k2_struct_0 @ sk_A) = (sk_B_1)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('clc', [status(thm)], ['14', '19'])).
% 0.47/0.66  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf('97', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (v3_pre_topc @ (k7_subset_1 @ sk_B_1 @ sk_B_1 @ X0) @ sk_A)
% 0.47/0.66           | (v4_pre_topc @ X0 @ sk_A)
% 0.47/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.47/0.66  thf('98', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.47/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf(dt_k7_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.66  thf('99', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.47/0.66          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.47/0.66  thf('100', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.66  thf('101', plain,
% 0.47/0.66      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.47/0.66  thf(t17_tdlat_3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ( v1_tdlat_3 @ A ) <=>
% 0.47/0.66         ( ![B:$i]:
% 0.47/0.66           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('102', plain,
% 0.47/0.66      (![X28 : $i, X29 : $i]:
% 0.47/0.66         (~ (v1_tdlat_3 @ X28)
% 0.47/0.66          | (v3_pre_topc @ X29 @ X28)
% 0.47/0.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.47/0.66          | ~ (l1_pre_topc @ X28)
% 0.47/0.66          | ~ (v2_pre_topc @ X28))),
% 0.47/0.66      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.47/0.66  thf('103', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.66           | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66           | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66           | (v3_pre_topc @ X0 @ sk_A)
% 0.47/0.66           | ~ (v1_tdlat_3 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['101', '102'])).
% 0.47/0.66  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('106', plain, ((v1_tdlat_3 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('107', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.66           | (v3_pre_topc @ X0 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.47/0.66  thf('108', plain,
% 0.47/0.66      ((![X0 : $i]: (v3_pre_topc @ (k7_subset_1 @ sk_B_1 @ sk_B_1 @ X0) @ sk_A))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['100', '107'])).
% 0.47/0.66  thf('109', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((v4_pre_topc @ X0 @ sk_A)
% 0.47/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['97', '108'])).
% 0.47/0.66  thf('110', plain,
% 0.47/0.66      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['90', '109'])).
% 0.47/0.66  thf('111', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t52_pre_topc, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.47/0.66             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.47/0.66               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.47/0.66  thf('112', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.66          | ~ (v4_pre_topc @ X18 @ X19)
% 0.47/0.66          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.47/0.66          | ~ (l1_pre_topc @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.47/0.66  thf('113', plain,
% 0.47/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.66        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.47/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['111', '112'])).
% 0.47/0.66  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('115', plain,
% 0.47/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.47/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['113', '114'])).
% 0.47/0.66  thf('116', plain,
% 0.47/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['110', '115'])).
% 0.47/0.66  thf('117', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['21', '58'])).
% 0.47/0.66  thf('118', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 0.47/0.66  thf('119', plain,
% 0.47/0.66      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['89', '118'])).
% 0.47/0.66  thf('120', plain,
% 0.47/0.66      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.47/0.66         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['119'])).
% 0.47/0.66  thf('121', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['21', '58'])).
% 0.47/0.66  thf('122', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['120', '121'])).
% 0.47/0.66  thf('123', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['81', '122'])).
% 0.47/0.66  thf('124', plain,
% 0.47/0.66      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['52'])).
% 0.47/0.66  thf('125', plain,
% 0.47/0.66      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.47/0.66       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['52'])).
% 0.47/0.66  thf('126', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['21', '58', '125'])).
% 0.47/0.66  thf('127', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['124', '126'])).
% 0.47/0.66  thf('128', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['123', '127'])).
% 0.47/0.66  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
