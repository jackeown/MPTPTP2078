%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgOnxwaO3N

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  207 (9304 expanded)
%              Number of leaves         :   34 (2694 expanded)
%              Depth                    :   24
%              Number of atoms          : 1636 (104713 expanded)
%              Number of equality atoms :   93 (5045 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t16_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
              = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tex_2])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( sk_C @ X29 @ X30 )
        = ( u1_struct_0 @ X29 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ~ ( v1_pre_topc @ X5 )
      | ( X5
        = ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( g1_pre_topc @ X18 @ X19 )
       != ( g1_pre_topc @ X16 @ X17 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('43',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('50',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('52',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','54'])).

thf('56',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','57'])).

thf('59',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('61',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('62',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('65',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('72',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['76','79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['71','80'])).

thf('82',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','84'])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( l1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('95',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k2_struct_0 @ X8 )
       != X6 )
      | ( X8
        = ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( X8
        = ( k1_pre_topc @ X7 @ ( k2_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('101',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('102',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('103',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('106',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('111',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X21 ) @ ( u1_pre_topc @ X21 ) ) )
      | ( m1_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['109','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('120',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','103','108','118','119'])).

thf('121',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('122',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,
    ( ( ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('125',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('126',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('129',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('130',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('132',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('133',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ( X8
        = ( k1_pre_topc @ X7 @ ( k2_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_B )
    | ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('139',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('140',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('142',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('144',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('146',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','144','145'])).

thf('147',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ( ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) )
      = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('151',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('152',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','144','145'])).

thf('153',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('156',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('158',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','144','145'])).

thf('160',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','146'])).

thf('162',plain,
    ( ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) )
    = ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','153','160','161'])).

thf('163',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','162'])).

thf('164',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('166',plain,(
    ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','70'])).

thf('168',plain,(
    ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
 != ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','144','145'])).

thf('170',plain,(
    ( k1_pre_topc @ sk_B @ ( k2_struct_0 @ sk_B ) )
 != ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['163','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgOnxwaO3N
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:23:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1453 iterations in 0.666s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.13  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.90/1.13  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.90/1.13  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.90/1.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.13  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.90/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.13  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.13  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.90/1.13  thf(d3_struct_0, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.13  thf('0', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf(t16_tex_2, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.13           ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.90/1.13             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13          ( ![B:$i]:
% 0.90/1.13            ( ( ( ~( v1_tex_2 @ B @ A ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.13              ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.90/1.13                ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t16_tex_2])).
% 0.90/1.13  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(d3_tex_2, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.13           ( ( v1_tex_2 @ B @ A ) <=>
% 0.90/1.13             ( ![C:$i]:
% 0.90/1.13               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.90/1.13                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X29 : $i, X30 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.13          | (m1_subset_1 @ (sk_C @ X29 @ X30) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.90/1.13          | (v1_tex_2 @ X29 @ X30)
% 0.90/1.13          | ~ (l1_pre_topc @ X30))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (v1_tex_2 @ sk_B @ sk_A)
% 0.90/1.13        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.13  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X29 : $i, X30 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.13          | ((sk_C @ X29 @ X30) = (u1_struct_0 @ X29))
% 0.90/1.13          | (v1_tex_2 @ X29 @ X30)
% 0.90/1.13          | ~ (l1_pre_topc @ X30))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (v1_tex_2 @ sk_B @ sk_A)
% 0.90/1.13        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t11_tmap_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.13           ( ( v1_pre_topc @
% 0.90/1.13               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.90/1.13             ( m1_pre_topc @
% 0.90/1.13               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X24 : $i, X25 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X24 @ X25)
% 0.90/1.13          | (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 0.90/1.13          | ~ (l1_pre_topc @ X25))),
% 0.90/1.13      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (v1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.13  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf(abstractness_v1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ( v1_pre_topc @ A ) =>
% 0.90/1.13         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X5 : $i]:
% 0.90/1.13         (~ (v1_pre_topc @ X5)
% 0.90/1.13          | ((X5) = (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.90/1.13          | ~ (l1_pre_topc @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.90/1.13  thf(dt_u1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( m1_subset_1 @
% 0.90/1.13         ( u1_pre_topc @ A ) @ 
% 0.90/1.13         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X15 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.90/1.13          | ~ (l1_pre_topc @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf(free_g1_pre_topc, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.13       ( ![C:$i,D:$i]:
% 0.90/1.13         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.90/1.13           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.90/1.13         (((g1_pre_topc @ X18 @ X19) != (g1_pre_topc @ X16 @ X17))
% 0.90/1.13          | ((X18) = (X16))
% 0.90/1.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.90/1.13      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | ((u1_struct_0 @ X0) = (X1))
% 0.90/1.13          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.90/1.13              != (g1_pre_topc @ X1 @ X2)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ X0)
% 0.90/1.13          | ~ (v1_pre_topc @ X0)
% 0.90/1.13          | ((u1_struct_0 @ X0) = (X2))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['15', '18'])).
% 0.90/1.13  thf('20', plain,
% 0.90/1.13      (![X1 : $i, X2 : $i]:
% 0.90/1.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.90/1.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['19'])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13        | ((u1_struct_0 @ 
% 0.90/1.13            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13            = (u1_struct_0 @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['14', '20'])).
% 0.90/1.13  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (![X24 : $i, X25 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X24 @ X25)
% 0.90/1.13          | (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)) @ X25)
% 0.90/1.13          | ~ (l1_pre_topc @ X25))),
% 0.90/1.13      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (m1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.13  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      ((m1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.13  thf(dt_m1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X13 : $i, X14 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X13 @ X14)
% 0.90/1.13          | (l1_pre_topc @ X13)
% 0.90/1.13          | ~ (l1_pre_topc @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (l1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.13  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      ((l1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['28', '29'])).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (((u1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (u1_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['21', '30'])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      ((((u1_struct_0 @ 
% 0.90/1.13          (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13          = (u1_struct_0 @ sk_B))
% 0.90/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['9', '31'])).
% 0.90/1.13  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (![X13 : $i, X14 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X13 @ X14)
% 0.90/1.13          | (l1_pre_topc @ X13)
% 0.90/1.13          | ~ (l1_pre_topc @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.13  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.90/1.13      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.13  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.13      inference('demod', [status(thm)], ['35', '36'])).
% 0.90/1.13  thf(dt_l1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.13  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('40', plain,
% 0.90/1.13      (((u1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (u1_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['32', '39'])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (((v1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.13  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (![X1 : $i, X2 : $i]:
% 0.90/1.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.90/1.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['19'])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13        | ((u1_struct_0 @ 
% 0.90/1.13            (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13            = (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['45', '46'])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      ((l1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['28', '29'])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      (((l1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.13  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('52', plain,
% 0.90/1.13      ((l1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51'])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      (((u1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['47', '52'])).
% 0.90/1.13  thf('54', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('55', plain,
% 0.90/1.13      (((v1_tex_2 @ sk_B @ sk_A)
% 0.90/1.13        | ((sk_C @ sk_B @ sk_A) = (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['7', '8', '54'])).
% 0.90/1.13  thf('56', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('57', plain, (((sk_C @ sk_B @ sk_A) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('clc', [status(thm)], ['55', '56'])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      (((v1_tex_2 @ sk_B @ sk_A)
% 0.90/1.13        | (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.13      inference('demod', [status(thm)], ['3', '4', '57'])).
% 0.90/1.13  thf('59', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('clc', [status(thm)], ['58', '59'])).
% 0.90/1.13  thf(d7_subset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.13       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      (![X32 : $i, X33 : $i]:
% 0.90/1.13         (((X33) = (X32))
% 0.90/1.13          | (v1_subset_1 @ X33 @ X32)
% 0.90/1.13          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.90/1.13  thf('62', plain,
% 0.90/1.13      (((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.13        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.13  thf('63', plain, (((sk_C @ sk_B @ sk_A) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('clc', [status(thm)], ['55', '56'])).
% 0.90/1.13  thf('64', plain,
% 0.90/1.13      (![X29 : $i, X30 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X29 @ X30)
% 0.90/1.13          | ~ (v1_subset_1 @ (sk_C @ X29 @ X30) @ (u1_struct_0 @ X30))
% 0.90/1.13          | (v1_tex_2 @ X29 @ X30)
% 0.90/1.13          | ~ (l1_pre_topc @ X30))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.90/1.13  thf('65', plain,
% 0.90/1.13      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.13        | (v1_tex_2 @ sk_B @ sk_A)
% 0.90/1.13        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.13  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('68', plain,
% 0.90/1.13      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.13        | (v1_tex_2 @ sk_B @ sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.90/1.13  thf('69', plain, (~ (v1_tex_2 @ sk_B @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('70', plain,
% 0.90/1.13      (~ (v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['68', '69'])).
% 0.90/1.13  thf('71', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('72', plain,
% 0.90/1.13      (![X15 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.90/1.13          | ~ (l1_pre_topc @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf(dt_g1_pre_topc, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.13       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.90/1.13         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.90/1.13  thf('73', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         ((v1_pre_topc @ (g1_pre_topc @ X10 @ X11))
% 0.90/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.90/1.13  thf('74', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.13  thf('75', plain,
% 0.90/1.13      (![X1 : $i, X2 : $i]:
% 0.90/1.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.90/1.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.90/1.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['19'])).
% 0.90/1.13  thf('76', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ 
% 0.90/1.13               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ((u1_struct_0 @ 
% 0.90/1.13              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13              = (u1_struct_0 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.13  thf('77', plain,
% 0.90/1.13      (![X15 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (u1_pre_topc @ X15) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.90/1.13          | ~ (l1_pre_topc @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.13  thf('78', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         ((l1_pre_topc @ (g1_pre_topc @ X10 @ X11))
% 0.90/1.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.90/1.13  thf('79', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.13  thf('80', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((u1_struct_0 @ 
% 0.90/1.13            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13            = (u1_struct_0 @ X0))
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('clc', [status(thm)], ['76', '79'])).
% 0.90/1.13  thf('81', plain,
% 0.90/1.13      ((((u1_struct_0 @ 
% 0.90/1.13          (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13          = (u1_struct_0 @ sk_A))
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup+', [status(thm)], ['71', '80'])).
% 0.90/1.13  thf('82', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('84', plain,
% 0.90/1.13      (((u1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.90/1.13  thf('85', plain,
% 0.90/1.13      ((((k2_struct_0 @ 
% 0.90/1.13          (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13          = (k2_struct_0 @ sk_B))
% 0.90/1.13        | ~ (l1_struct_0 @ 
% 0.90/1.13             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))),
% 0.90/1.13      inference('sup+', [status(thm)], ['0', '84'])).
% 0.90/1.13  thf('86', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('87', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.13  thf('88', plain,
% 0.90/1.13      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.13  thf('89', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_struct_0 @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.13  thf('90', plain,
% 0.90/1.13      (((l1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup+', [status(thm)], ['86', '89'])).
% 0.90/1.13  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('92', plain,
% 0.90/1.13      ((l1_struct_0 @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['90', '91'])).
% 0.90/1.13  thf('93', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['85', '92'])).
% 0.90/1.13  thf('94', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf(d10_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.13           ( ![C:$i]:
% 0.90/1.13             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.13               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.90/1.13                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf('95', plain,
% 0.90/1.13      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.90/1.13          | ((k2_struct_0 @ X8) != (X6))
% 0.90/1.13          | ((X8) = (k1_pre_topc @ X7 @ X6))
% 0.90/1.13          | ~ (m1_pre_topc @ X8 @ X7)
% 0.90/1.13          | ~ (v1_pre_topc @ X8)
% 0.90/1.13          | ~ (l1_pre_topc @ X7))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.90/1.13  thf('96', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X7)
% 0.90/1.13          | ~ (v1_pre_topc @ X8)
% 0.90/1.13          | ~ (m1_pre_topc @ X8 @ X7)
% 0.90/1.13          | ((X8) = (k1_pre_topc @ X7 @ (k2_struct_0 @ X8)))
% 0.90/1.13          | ~ (m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.90/1.13               (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf('97', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13          | ((X0) = (k1_pre_topc @ sk_A @ (k2_struct_0 @ X0)))
% 0.90/1.13          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.90/1.13          | ~ (v1_pre_topc @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['94', '96'])).
% 0.90/1.13  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('99', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13          | ((X0) = (k1_pre_topc @ sk_A @ (k2_struct_0 @ X0)))
% 0.90/1.13          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.90/1.13          | ~ (v1_pre_topc @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['97', '98'])).
% 0.90/1.13  thf('100', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13        | ~ (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13        | ~ (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 0.90/1.13        | ((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.13            = (k1_pre_topc @ sk_A @ 
% 0.90/1.13               (k2_struct_0 @ 
% 0.90/1.13                (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['93', '99'])).
% 0.90/1.13  thf(dt_k2_subset_1, axiom,
% 0.90/1.13    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.13  thf('101', plain,
% 0.90/1.13      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.90/1.13  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.90/1.13  thf('102', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.90/1.13      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.90/1.13  thf('103', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.90/1.13      inference('demod', [status(thm)], ['101', '102'])).
% 0.90/1.13  thf('104', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('105', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.13  thf('106', plain,
% 0.90/1.13      (((v1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup+', [status(thm)], ['104', '105'])).
% 0.90/1.13  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('108', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['106', '107'])).
% 0.90/1.13  thf('109', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('110', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.13  thf(t2_tsep_1, axiom,
% 0.90/1.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.90/1.13  thf('111', plain,
% 0.90/1.13      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.90/1.13      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.13  thf(t59_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_pre_topc @
% 0.90/1.13             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.90/1.13           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.90/1.13  thf('112', plain,
% 0.90/1.13      (![X20 : $i, X21 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X20 @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X21) @ (u1_pre_topc @ X21)))
% 0.90/1.13          | (m1_pre_topc @ X20 @ X21)
% 0.90/1.13          | ~ (l1_pre_topc @ X21))),
% 0.90/1.13      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.90/1.13  thf('113', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ~ (l1_pre_topc @ X0)
% 0.90/1.13          | (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['111', '112'])).
% 0.90/1.13  thf('114', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X0)
% 0.90/1.13          | (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['110', '113'])).
% 0.90/1.13  thf('115', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((m1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['114'])).
% 0.90/1.13  thf('116', plain,
% 0.90/1.13      (((m1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 0.90/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.13      inference('sup+', [status(thm)], ['109', '115'])).
% 0.90/1.13  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('118', plain,
% 0.90/1.13      ((m1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['116', '117'])).
% 0.90/1.13  thf('119', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['85', '92'])).
% 0.90/1.13  thf('120', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.13         = (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['100', '103', '108', '118', '119'])).
% 0.90/1.13  thf('121', plain,
% 0.90/1.13      (((u1_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (u1_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['21', '30'])).
% 0.90/1.13  thf('122', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf('123', plain,
% 0.90/1.13      ((((k2_struct_0 @ 
% 0.90/1.13          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13          = (u1_struct_0 @ sk_B))
% 0.90/1.13        | ~ (l1_struct_0 @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.90/1.13      inference('sup+', [status(thm)], ['121', '122'])).
% 0.90/1.13  thf('124', plain,
% 0.90/1.13      ((l1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['28', '29'])).
% 0.90/1.13  thf('125', plain,
% 0.90/1.13      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.13  thf('126', plain,
% 0.90/1.13      ((l1_struct_0 @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['124', '125'])).
% 0.90/1.13  thf('127', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (u1_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['123', '126'])).
% 0.90/1.13  thf('128', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('129', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('130', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.90/1.13  thf('131', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.90/1.13  thf('132', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('133', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ X7)
% 0.90/1.13          | ~ (v1_pre_topc @ X8)
% 0.90/1.13          | ~ (m1_pre_topc @ X8 @ X7)
% 0.90/1.13          | ((X8) = (k1_pre_topc @ X7 @ (k2_struct_0 @ X8)))
% 0.90/1.13          | ~ (m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.90/1.13               (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf('134', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13          | ((X0) = (k1_pre_topc @ sk_B @ (k2_struct_0 @ X0)))
% 0.90/1.13          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.13          | ~ (v1_pre_topc @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.13      inference('sup-', [status(thm)], ['132', '133'])).
% 0.90/1.13  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.13      inference('demod', [status(thm)], ['35', '36'])).
% 0.90/1.13  thf('136', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13          | ((X0) = (k1_pre_topc @ sk_B @ (k2_struct_0 @ X0)))
% 0.90/1.13          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.90/1.13          | ~ (v1_pre_topc @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['134', '135'])).
% 0.90/1.13  thf('137', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13        | ~ (v1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13        | ~ (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_B)
% 0.90/1.13        | ((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13            = (k1_pre_topc @ sk_B @ 
% 0.90/1.13               (k2_struct_0 @ 
% 0.90/1.13                (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['131', '136'])).
% 0.90/1.13  thf('138', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.90/1.13      inference('demod', [status(thm)], ['101', '102'])).
% 0.90/1.13  thf('139', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('140', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('141', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((m1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.90/1.13          | ~ (l1_pre_topc @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['114'])).
% 0.90/1.13  thf('142', plain,
% 0.90/1.13      (((m1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_B)
% 0.90/1.13        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['140', '141'])).
% 0.90/1.13  thf('143', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.13      inference('demod', [status(thm)], ['35', '36'])).
% 0.90/1.13  thf('144', plain,
% 0.90/1.13      ((m1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_B)),
% 0.90/1.13      inference('demod', [status(thm)], ['142', '143'])).
% 0.90/1.13  thf('145', plain,
% 0.90/1.13      (((k2_struct_0 @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.90/1.13  thf('146', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         = (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['137', '138', '139', '144', '145'])).
% 0.90/1.13  thf('147', plain,
% 0.90/1.13      (((k2_struct_0 @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['130', '146'])).
% 0.90/1.13  thf('148', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13          | ((X0) = (k1_pre_topc @ sk_A @ (k2_struct_0 @ X0)))
% 0.90/1.13          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.90/1.13          | ~ (v1_pre_topc @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['97', '98'])).
% 0.90/1.13  thf('149', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.90/1.13        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))
% 0.90/1.13        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.90/1.13        | ((k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B))
% 0.90/1.13            = (k1_pre_topc @ sk_A @ 
% 0.90/1.13               (k2_struct_0 @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B))))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['147', '148'])).
% 0.90/1.13  thf('150', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.90/1.13      inference('demod', [status(thm)], ['101', '102'])).
% 0.90/1.13  thf('151', plain,
% 0.90/1.13      ((v1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('152', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         = (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['137', '138', '139', '144', '145'])).
% 0.90/1.13  thf('153', plain,
% 0.90/1.13      ((v1_pre_topc @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['151', '152'])).
% 0.90/1.13  thf('154', plain,
% 0.90/1.13      (![X9 : $i]:
% 0.90/1.13         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.13  thf('155', plain,
% 0.90/1.13      ((m1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.13  thf('156', plain,
% 0.90/1.13      (((m1_pre_topc @ 
% 0.90/1.13         (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)
% 0.90/1.13        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['154', '155'])).
% 0.90/1.13  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('158', plain,
% 0.90/1.13      ((m1_pre_topc @ 
% 0.90/1.13        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['156', '157'])).
% 0.90/1.13  thf('159', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         = (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['137', '138', '139', '144', '145'])).
% 0.90/1.13  thf('160', plain,
% 0.90/1.13      ((m1_pre_topc @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['158', '159'])).
% 0.90/1.13  thf('161', plain,
% 0.90/1.13      (((k2_struct_0 @ (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))
% 0.90/1.13         = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['130', '146'])).
% 0.90/1.13  thf('162', plain,
% 0.90/1.13      (((k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B))
% 0.90/1.13         = (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['149', '150', '153', '160', '161'])).
% 0.90/1.13  thf('163', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.13         = (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['120', '162'])).
% 0.90/1.13  thf('164', plain,
% 0.90/1.13      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('165', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['40', '53'])).
% 0.90/1.13  thf('166', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         != (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['164', '165'])).
% 0.90/1.13  thf('167', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.90/1.13      inference('clc', [status(thm)], ['62', '70'])).
% 0.90/1.13  thf('168', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         != (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['166', '167'])).
% 0.90/1.13  thf('169', plain,
% 0.90/1.13      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.90/1.13         = (k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B)))),
% 0.90/1.13      inference('demod', [status(thm)], ['137', '138', '139', '144', '145'])).
% 0.90/1.13  thf('170', plain,
% 0.90/1.13      (((k1_pre_topc @ sk_B @ (k2_struct_0 @ sk_B))
% 0.90/1.13         != (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['168', '169'])).
% 0.90/1.13  thf('171', plain, ($false),
% 0.90/1.13      inference('simplify_reflect-', [status(thm)], ['163', '170'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
