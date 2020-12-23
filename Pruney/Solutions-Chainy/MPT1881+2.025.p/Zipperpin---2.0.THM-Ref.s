%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wWUV52PWLO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 243 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  826 (2483 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( v1_subset_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( v2_tex_2 @ X17 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
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
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('36',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ X2 @ X2 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','39'])).

thf('41',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( v1_subset_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X9: $i] :
      ( ( ( k2_pre_topc @ X9 @ ( k2_struct_0 @ X9 ) )
        = ( k2_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_pre_topc @ X12 @ X11 )
       != ( u1_struct_0 @ X12 ) )
      | ( v1_tops_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('58',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['41','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('73',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('74',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','39','73'])).

thf('75',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['71','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wWUV52PWLO
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 231 iterations in 0.076s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
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
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((X14) = (X13))
% 0.21/0.53          | (v1_subset_1 @ X14 @ X13)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
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
% 0.21/0.53      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('9', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('10', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t43_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.53          | (v2_tex_2 @ X18 @ X19)
% 0.21/0.53          | ~ (l1_pre_topc @ X19)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X19)
% 0.21/0.53          | ~ (v2_pre_topc @ X19)
% 0.21/0.53          | (v2_struct_0 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
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
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (v3_tex_2 @ X15 @ X16)
% 0.21/0.53          | ~ (v2_tex_2 @ X17 @ X16)
% 0.21/0.53          | ~ (r1_tarski @ X15 @ X17)
% 0.21/0.53          | ((X15) = (X17))
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.53          | ~ (l1_pre_topc @ X16))),
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
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_A)
% 0.21/0.53         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '25'])).
% 0.21/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.21/0.53  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ sk_B))
% 0.21/0.53         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.21/0.53             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['32', '34'])).
% 0.21/0.53  thf(fc14_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.53  thf('36', plain, (![X2 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X2) @ X2)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.53  thf('37', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('38', plain, (![X2 : $i]: ~ (v1_subset_1 @ X2 @ X2)),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.53       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.53  thf('40', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '39'])).
% 0.21/0.53  thf('41', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['6', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf(dt_k2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) =>
% 0.21/0.53       ( m1_subset_1 @
% 0.21/0.53         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X6 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.53          | ~ (l1_struct_0 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((X14) = (X13))
% 0.21/0.53          | (v1_subset_1 @ X14 @ X13)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v1_subset_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.21/0.53          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf(fc12_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) =>
% 0.21/0.53       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X8 : $i]:
% 0.21/0.53         (~ (v1_subset_1 @ (k2_struct_0 @ X8) @ (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (l1_struct_0 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf(t27_tops_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X9 : $i]:
% 0.21/0.53         (((k2_pre_topc @ X9 @ (k2_struct_0 @ X9)) = (k2_struct_0 @ X9))
% 0.21/0.53          | ~ (l1_pre_topc @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('50', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(d2_tops_3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.53          | ((k2_pre_topc @ X12 @ X11) != (u1_struct_0 @ X12))
% 0.21/0.53          | (v1_tops_1 @ X11 @ X12)
% 0.21/0.53          | ~ (l1_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k2_struct_0 @ X0) != (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '55'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('58', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.53  thf('60', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t48_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.53             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.53          | (v3_tex_2 @ X20 @ X21)
% 0.21/0.53          | ~ (v2_tex_2 @ X20 @ X21)
% 0.21/0.53          | ~ (v1_tops_1 @ X20 @ X21)
% 0.21/0.53          | ~ (l1_pre_topc @ X21)
% 0.21/0.53          | ~ (v2_pre_topc @ X21)
% 0.21/0.53          | (v2_struct_0 @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '66'])).
% 0.21/0.53  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.53       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['33'])).
% 0.21/0.53  thf('74', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['7', '39', '73'])).
% 0.21/0.53  thf('75', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.21/0.53  thf('76', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['71', '75'])).
% 0.21/0.53  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
