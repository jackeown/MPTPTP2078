%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bXE6Pj1lyj

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:18 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  154 (1353 expanded)
%              Number of leaves         :   29 ( 413 expanded)
%              Depth                    :   25
%              Number of atoms          : 1161 (14317 expanded)
%              Number of equality atoms :   43 ( 347 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
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
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
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
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
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
    ! [X16: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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

thf('22',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('23',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v2_tex_2 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('27',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(fc12_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('36',plain,(
    ! [X28: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v1_tops_1 @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k2_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v1_tops_1 @ X32 @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

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

thf('54',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_tex_2 @ X36 @ X37 )
      | ~ ( v2_tex_2 @ X38 @ X37 )
      | ~ ( r1_tarski @ X36 @ X38 )
      | ( X36 = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1 = X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( v2_tex_2 @ X2 @ X0 )
      | ~ ( v3_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_tex_2 @ X1 @ X0 )
      | ~ ( v2_tex_2 @ X2 @ X0 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( X1 = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( X1
        = ( k2_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','56'])).

thf('58',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('65',plain,(
    r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('68',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( sk_B_1
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','65','66','67'])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('79',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( ( v1_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('83',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','76'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('87',plain,(
    ! [X16: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','76'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('93',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','94'])).

thf('96',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['20','95'])).

thf('97',plain,(
    ! [X28: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf('98',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
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

thf('99',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v3_tex_2 @ X43 @ X44 )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ~ ( v1_tops_1 @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v2_tex_2 @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['20','95'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('117',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','112','113','114','115','116'])).

thf('118',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['79'])).

thf('119',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['79'])).

thf('120',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['21','94','119'])).

thf('121',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['118','120'])).

thf('122',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['117','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bXE6Pj1lyj
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 537 iterations in 0.269s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.50/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.50/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.73  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.50/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.73  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.50/0.73  thf(t49_tex_2, conjecture,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.50/0.73         ( l1_pre_topc @ A ) ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v3_tex_2 @ B @ A ) <=>
% 0.50/0.73             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i]:
% 0.50/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.50/0.73            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.73          ( ![B:$i]:
% 0.50/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73              ( ( v3_tex_2 @ B @ A ) <=>
% 0.50/0.73                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.50/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(d7_subset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.73       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X34 : $i, X35 : $i]:
% 0.50/0.73         (((X35) = (X34))
% 0.50/0.73          | (v1_subset_1 @ X35 @ X34)
% 0.50/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.50/0.73        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.50/0.73        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('split', [status(esa)], ['4'])).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['3', '5'])).
% 0.50/0.73  thf(dt_k2_struct_0, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_struct_0 @ A ) =>
% 0.50/0.73       ( m1_subset_1 @
% 0.50/0.73         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      ((((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.50/0.73         | ~ (l1_struct_0 @ sk_A)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup+', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(dt_l1_pre_topc, axiom,
% 0.50/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.73  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('demod', [status(thm)], ['8', '11'])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X34 : $i, X35 : $i]:
% 0.50/0.73         (((X35) = (X34))
% 0.50/0.73          | (v1_subset_1 @ X35 @ X34)
% 0.50/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      ((((v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.50/0.73         | ((k2_struct_0 @ sk_A) = (sk_B_1))))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['3', '5'])).
% 0.50/0.73  thf(fc12_struct_0, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_struct_0 @ A ) =>
% 0.50/0.73       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      (![X16 : $i]:
% 0.50/0.73         (~ (v1_subset_1 @ (k2_struct_0 @ X16) @ (u1_struct_0 @ X16))
% 0.50/0.73          | ~ (l1_struct_0 @ X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.50/0.73         | ~ (l1_struct_0 @ sk_A)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.73  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      ((((k2_struct_0 @ sk_A) = (sk_B_1)))
% 0.50/0.73         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('clc', [status(thm)], ['14', '19'])).
% 0.50/0.73  thf('21', plain,
% 0.50/0.73      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.50/0.73       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('split', [status(esa)], ['4'])).
% 0.50/0.73  thf('22', plain,
% 0.50/0.73      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('split', [status(esa)], ['4'])).
% 0.50/0.73  thf('23', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf(t43_tex_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.50/0.73         ( l1_pre_topc @ A ) ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      (![X41 : $i, X42 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.50/0.73          | (v2_tex_2 @ X41 @ X42)
% 0.50/0.73          | ~ (l1_pre_topc @ X42)
% 0.50/0.73          | ~ (v1_tdlat_3 @ X42)
% 0.50/0.73          | ~ (v2_pre_topc @ X42)
% 0.50/0.73          | (v2_struct_0 @ X42))),
% 0.50/0.73      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | (v2_struct_0 @ X0)
% 0.50/0.73          | ~ (v2_pre_topc @ X0)
% 0.50/0.73          | ~ (v1_tdlat_3 @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | (v2_tex_2 @ (k2_struct_0 @ X0) @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.73  thf('26', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (![X34 : $i, X35 : $i]:
% 0.50/0.73         (((X35) = (X34))
% 0.50/0.73          | (v1_subset_1 @ X35 @ X34)
% 0.50/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | (v1_subset_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.50/0.73          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.73  thf('29', plain,
% 0.50/0.73      (![X16 : $i]:
% 0.50/0.73         (~ (v1_subset_1 @ (k2_struct_0 @ X16) @ (u1_struct_0 @ X16))
% 0.50/0.73          | ~ (l1_struct_0 @ X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.50/0.73  thf('30', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.50/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.50/0.73  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('34', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['32', '33'])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf(fc12_tops_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.50/0.73  thf('36', plain,
% 0.50/0.73      (![X28 : $i]:
% 0.50/0.73         ((v1_tops_1 @ (k2_struct_0 @ X28) @ X28) | ~ (l1_pre_topc @ X28))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf(d3_tops_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v1_tops_1 @ B @ A ) <=>
% 0.50/0.73             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('38', plain,
% 0.50/0.73      (![X26 : $i, X27 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.50/0.73          | ~ (v1_tops_1 @ X26 @ X27)
% 0.50/0.73          | ((k2_pre_topc @ X27 @ X26) = (k2_struct_0 @ X27))
% 0.50/0.73          | ~ (l1_pre_topc @ X27))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['36', '39'])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_pre_topc @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.50/0.73      inference('clc', [status(thm)], ['41', '42'])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      (![X28 : $i]:
% 0.50/0.73         ((v1_tops_1 @ (k2_struct_0 @ X28) @ X28) | ~ (l1_pre_topc @ X28))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.50/0.73  thf('45', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf(d2_tops_3, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v1_tops_1 @ B @ A ) <=>
% 0.50/0.73             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('46', plain,
% 0.50/0.73      (![X32 : $i, X33 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.50/0.73          | ~ (v1_tops_1 @ X32 @ X33)
% 0.50/0.73          | ((k2_pre_topc @ X33 @ X32) = (u1_struct_0 @ X33))
% 0.50/0.73          | ~ (l1_pre_topc @ X33))),
% 0.50/0.73      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.50/0.73          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.73  thf('48', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['44', '47'])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_pre_topc @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['48'])).
% 0.50/0.73  thf('50', plain,
% 0.50/0.73      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.73  thf('51', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.50/0.73      inference('clc', [status(thm)], ['49', '50'])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['43', '51'])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['52'])).
% 0.50/0.73  thf(d7_tex_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v3_tex_2 @ B @ A ) <=>
% 0.50/0.73             ( ( v2_tex_2 @ B @ A ) & 
% 0.50/0.73               ( ![C:$i]:
% 0.50/0.73                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.73                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf('54', plain,
% 0.50/0.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.50/0.73          | ~ (v3_tex_2 @ X36 @ X37)
% 0.50/0.73          | ~ (v2_tex_2 @ X38 @ X37)
% 0.50/0.73          | ~ (r1_tarski @ X36 @ X38)
% 0.50/0.73          | ((X36) = (X38))
% 0.50/0.73          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.50/0.73          | ~ (l1_pre_topc @ X37))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.73  thf('55', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.73          | ((X1) = (X2))
% 0.50/0.73          | ~ (r1_tarski @ X1 @ X2)
% 0.50/0.73          | ~ (v2_tex_2 @ X2 @ X0)
% 0.50/0.73          | ~ (v3_tex_2 @ X1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.50/0.73  thf('56', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v3_tex_2 @ X1 @ X0)
% 0.50/0.73          | ~ (v2_tex_2 @ X2 @ X0)
% 0.50/0.73          | ~ (r1_tarski @ X1 @ X2)
% 0.50/0.73          | ((X1) = (X2))
% 0.50/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.50/0.73      inference('simplify', [status(thm)], ['55'])).
% 0.50/0.73  thf('57', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ((X1) = (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (r1_tarski @ X1 @ (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (v2_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | ~ (v3_tex_2 @ X1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['35', '56'])).
% 0.50/0.73  thf('58', plain,
% 0.50/0.73      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.50/0.73        | ~ (v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.50/0.73        | ~ (r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.50/0.73        | ((sk_B_1) = (k2_struct_0 @ sk_A))
% 0.50/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['34', '57'])).
% 0.50/0.73  thf('59', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('60', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(t3_subset, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.73  thf('61', plain,
% 0.50/0.73      (![X11 : $i, X12 : $i]:
% 0.50/0.73         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('62', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.73  thf('63', plain,
% 0.50/0.73      (((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup+', [status(thm)], ['59', '62'])).
% 0.50/0.73  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('65', plain, ((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['63', '64'])).
% 0.50/0.73  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('68', plain,
% 0.50/0.73      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.50/0.73        | ~ (v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.50/0.73        | ((sk_B_1) = (k2_struct_0 @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['58', '65', '66', '67'])).
% 0.50/0.73  thf('69', plain,
% 0.50/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | ~ (v1_tdlat_3 @ sk_A)
% 0.50/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.73        | (v2_struct_0 @ sk_A)
% 0.50/0.73        | ~ (l1_struct_0 @ sk_A)
% 0.50/0.73        | ((sk_B_1) = (k2_struct_0 @ sk_A))
% 0.50/0.73        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '68'])).
% 0.50/0.73  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('71', plain, ((v1_tdlat_3 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('74', plain,
% 0.50/0.73      (((v2_struct_0 @ sk_A)
% 0.50/0.73        | ((sk_B_1) = (k2_struct_0 @ sk_A))
% 0.50/0.73        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.50/0.73  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('76', plain,
% 0.50/0.73      ((~ (v3_tex_2 @ sk_B_1 @ sk_A) | ((sk_B_1) = (k2_struct_0 @ sk_A)))),
% 0.50/0.73      inference('clc', [status(thm)], ['74', '75'])).
% 0.50/0.73  thf('77', plain,
% 0.50/0.73      ((((sk_B_1) = (k2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['22', '76'])).
% 0.50/0.73  thf('78', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('79', plain,
% 0.50/0.73      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.50/0.73        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('80', plain,
% 0.50/0.73      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('split', [status(esa)], ['79'])).
% 0.50/0.73  thf('81', plain,
% 0.50/0.73      ((((v1_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.50/0.73         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup+', [status(thm)], ['78', '80'])).
% 0.50/0.73  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('83', plain,
% 0.50/0.73      (((v1_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A)))
% 0.50/0.73         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('demod', [status(thm)], ['81', '82'])).
% 0.50/0.73  thf('84', plain,
% 0.50/0.73      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.50/0.73         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.50/0.73             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('sup+', [status(thm)], ['77', '83'])).
% 0.50/0.73  thf('85', plain,
% 0.50/0.73      ((((sk_B_1) = (k2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['22', '76'])).
% 0.50/0.73  thf('86', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('87', plain,
% 0.50/0.73      (![X16 : $i]:
% 0.50/0.73         (~ (v1_subset_1 @ (k2_struct_0 @ X16) @ (u1_struct_0 @ X16))
% 0.50/0.73          | ~ (l1_struct_0 @ X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.50/0.73  thf('88', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.50/0.73          | ~ (l1_struct_0 @ X0)
% 0.50/0.73          | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['86', '87'])).
% 0.50/0.73  thf('89', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | ~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['88'])).
% 0.50/0.73  thf('90', plain,
% 0.50/0.73      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.50/0.73         | ~ (l1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['85', '89'])).
% 0.50/0.73  thf('91', plain,
% 0.50/0.73      ((((sk_B_1) = (k2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['22', '76'])).
% 0.50/0.73  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('93', plain,
% 0.50/0.73      ((~ (v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.50/0.73  thf('94', plain,
% 0.50/0.73      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.50/0.73       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['84', '93'])).
% 0.50/0.73  thf('95', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['21', '94'])).
% 0.50/0.73  thf('96', plain, (((k2_struct_0 @ sk_A) = (sk_B_1))),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['20', '95'])).
% 0.50/0.73  thf('97', plain,
% 0.50/0.73      (![X28 : $i]:
% 0.50/0.73         ((v1_tops_1 @ (k2_struct_0 @ X28) @ X28) | ~ (l1_pre_topc @ X28))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.50/0.73  thf('98', plain,
% 0.50/0.73      (![X14 : $i]:
% 0.50/0.73         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (l1_struct_0 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.50/0.73  thf(t48_tex_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.50/0.73             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.50/0.73  thf('99', plain,
% 0.50/0.73      (![X43 : $i, X44 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.50/0.73          | (v3_tex_2 @ X43 @ X44)
% 0.50/0.73          | ~ (v2_tex_2 @ X43 @ X44)
% 0.50/0.73          | ~ (v1_tops_1 @ X43 @ X44)
% 0.50/0.73          | ~ (l1_pre_topc @ X44)
% 0.50/0.73          | ~ (v2_pre_topc @ X44)
% 0.50/0.73          | (v2_struct_0 @ X44))),
% 0.50/0.73      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.50/0.73  thf('100', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | (v2_struct_0 @ X0)
% 0.50/0.73          | ~ (v2_pre_topc @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | ~ (v2_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | (v3_tex_2 @ (k2_struct_0 @ X0) @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['98', '99'])).
% 0.50/0.73  thf('101', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X0)
% 0.50/0.73          | (v3_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | ~ (v2_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0)
% 0.50/0.73          | ~ (v2_pre_topc @ X0)
% 0.50/0.73          | (v2_struct_0 @ X0)
% 0.50/0.73          | ~ (l1_struct_0 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['97', '100'])).
% 0.50/0.73  thf('102', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_struct_0 @ X0)
% 0.50/0.73          | (v2_struct_0 @ X0)
% 0.50/0.73          | ~ (v2_pre_topc @ X0)
% 0.50/0.73          | ~ (v2_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | (v3_tex_2 @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.73          | ~ (l1_pre_topc @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['101'])).
% 0.50/0.73  thf('103', plain,
% 0.50/0.73      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.50/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | (v3_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.50/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.73        | (v2_struct_0 @ sk_A)
% 0.50/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['96', '102'])).
% 0.50/0.73  thf('104', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('105', plain,
% 0.50/0.73      (![X41 : $i, X42 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.50/0.73          | (v2_tex_2 @ X41 @ X42)
% 0.50/0.73          | ~ (l1_pre_topc @ X42)
% 0.50/0.73          | ~ (v1_tdlat_3 @ X42)
% 0.50/0.73          | ~ (v2_pre_topc @ X42)
% 0.50/0.73          | (v2_struct_0 @ X42))),
% 0.50/0.73      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.50/0.73  thf('106', plain,
% 0.50/0.73      (((v2_struct_0 @ sk_A)
% 0.50/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.73        | ~ (v1_tdlat_3 @ sk_A)
% 0.50/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['104', '105'])).
% 0.50/0.73  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('108', plain, ((v1_tdlat_3 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('110', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.50/0.73  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('112', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.50/0.73      inference('clc', [status(thm)], ['110', '111'])).
% 0.50/0.73  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('114', plain, (((k2_struct_0 @ sk_A) = (sk_B_1))),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['20', '95'])).
% 0.50/0.73  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('117', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)],
% 0.50/0.73                ['103', '112', '113', '114', '115', '116'])).
% 0.50/0.73  thf('118', plain,
% 0.50/0.73      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.50/0.73      inference('split', [status(esa)], ['79'])).
% 0.50/0.73  thf('119', plain,
% 0.50/0.73      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.50/0.73       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('split', [status(esa)], ['79'])).
% 0.50/0.73  thf('120', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['21', '94', '119'])).
% 0.50/0.73  thf('121', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['118', '120'])).
% 0.50/0.73  thf('122', plain, ((v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('clc', [status(thm)], ['117', '121'])).
% 0.50/0.73  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
