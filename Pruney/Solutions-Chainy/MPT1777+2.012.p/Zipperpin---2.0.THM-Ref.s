%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eiK3Mlqjbn

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:28 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  403 (14347 expanded)
%              Number of leaves         :   48 (4253 expanded)
%              Depth                    :   40
%              Number of atoms          : 4145 (387003 expanded)
%              Number of equality atoms :  133 (12746 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t88_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                          = D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                 => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                            = D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                   => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( g1_pre_topc @ X13 @ X14 )
       != ( g1_pre_topc @ X11 @ X12 ) )
      | ( X13 = X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('21',plain,
    ( ( v1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('29',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf('31',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('38',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('45',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','27','28'])).

thf('47',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('49',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['42','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('62',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( m1_pre_topc @ X22 @ ( g1_pre_topc @ ( u1_struct_0 @ X21 ) @ ( u1_pre_topc @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf('67',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X31 )
      | ( ( k3_tmap_1 @ X30 @ X28 @ X31 @ X29 @ X32 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X28 ) @ X32 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('86',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('88',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','90'])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('93',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) @ X27 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('103',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('104',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('106',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('107',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103','104','105','106','107'])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('111',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['40','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('129',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t67_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('130',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( v1_tsep_1 @ X40 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ( r1_tmap_1 @ X39 @ X42 @ X43 @ X44 )
      | ( X44 != X41 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('131',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X39 @ X42 @ X43 @ X41 )
      | ~ ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( v1_tsep_1 @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_tsep_1 @ X3 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X1 @ ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 ) @ X4 )
      | ( r1_tmap_1 @ X0 @ X1 @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('138',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('139',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('140',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('141',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('142',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139','140','141','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','143'])).

thf('145',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('146',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('148',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('149',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( X35
       != ( u1_struct_0 @ X33 ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( v1_tsep_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('150',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tsep_1 @ X33 @ X34 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X33 ) @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('154',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('155',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ) )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf('158',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('159',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('160',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('161',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('162',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['3','10'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( v3_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161','162'])).

thf('164',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['153','163'])).

thf('165',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('166',plain,(
    ! [X23: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('167',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('170',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('175',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['167','173','174'])).

thf('176',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['164','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('178',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('179',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('180',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ ( g1_pre_topc @ ( u1_struct_0 @ X21 ) @ ( u1_pre_topc @ X21 ) ) )
      | ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('187',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['152','176','177','178','187'])).

thf('189',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['185','186'])).

thf('190',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('191',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('197',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','188','189','190','197','198'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('206',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('207',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( v1_tsep_1 @ X40 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r1_tmap_1 @ X39 @ X42 @ X43 @ X44 )
      | ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ( X44 != X41 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('208',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ~ ( r1_tmap_1 @ X39 @ X42 @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( v1_tsep_1 @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_tsep_1 @ X3 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X0 @ X1 @ X2 @ X4 )
      | ( r1_tmap_1 @ X3 @ X1 @ ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['206','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','209'])).

thf('211',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('215',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('216',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('217',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('218',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('219',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211','212','213','214','215','216','217','218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','220'])).

thf('222',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( v1_tsep_1 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('226',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('228',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ ( g1_pre_topc @ ( u1_struct_0 @ X21 ) @ ( u1_pre_topc @ X21 ) ) )
      | ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['226','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('233',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('235',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103','104','105','106','107'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('245',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('247',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('248',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('249',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tsep_1 @ X33 @ X34 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X33 ) @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_C )
      | ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('252',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_C )
      | ( v1_tsep_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ( v1_tsep_1 @ sk_D @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['247','253'])).

thf('255',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('256',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('257',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['164','175'])).

thf('258',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('259',plain,(
    v1_tsep_1 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['254','255','256','257','258'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['224','225','245','246','259'])).

thf('261',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('262',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('263',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('264',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( k2_tmap_1 @ X26 @ X24 @ X27 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) @ X27 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('265',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('267',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('268',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('269',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['262','270'])).

thf('272',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('275',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['271','272','273','274','275'])).

thf('277',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['261','276'])).

thf('278',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('279',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('280',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['277','278','279','280'])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['281','282'])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['283','284'])).

thf('286',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('287',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('288',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ( r1_tmap_1 @ X39 @ X42 @ X43 @ X41 )
      | ~ ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( v1_tsep_1 @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('291',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('292',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('293',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['289','290','291','292','293'])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['286','294'])).

thf('296',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('300',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['295','296','297','298','299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_D @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['285','300'])).

thf('302',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('304',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['167','173','174'])).

thf('306',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('307',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('308',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('309',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('310',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('314',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('318',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('320',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','27','28'])).

thf('321',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['318','319','320'])).

thf('322',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['315','321'])).

thf('323',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('324',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','27','28'])).

thf('325',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('327',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('329',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('331',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('333',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_D ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,
    ( ( m1_pre_topc @ sk_D @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['308','333'])).

thf('335',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('336',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','27','28'])).

thf('337',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['334','335','336'])).

thf('338',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['304','305','306','307','337'])).

thf('339',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['334','335','336'])).

thf('340',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['18','29','30','35','36'])).

thf('341',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['301','338','339','340'])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['260','342'])).

thf('344',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('345',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['345'])).

thf('347',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['348','349'])).

thf('351',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['350','351'])).

thf('353',plain,(
    $false ),
    inference(demod,[status(thm)],['0','352'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eiK3Mlqjbn
% 0.07/0.28  % Computer   : n007.cluster.edu
% 0.07/0.28  % Model      : x86_64 x86_64
% 0.07/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.28  % Memory     : 8042.1875MB
% 0.07/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.28  % CPULimit   : 60
% 0.07/0.28  % DateTime   : Tue Dec  1 17:14:21 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.07/0.28  % Running portfolio for 600 s
% 0.07/0.28  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.07/0.28  % Number of cores: 8
% 0.07/0.28  % Python version: Python 3.6.8
% 0.13/0.28  % Running in FO mode
% 1.14/1.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.33  % Solved by: fo/fo7.sh
% 1.14/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.33  % done 1713 iterations in 0.971s
% 1.14/1.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.33  % SZS output start Refutation
% 1.14/1.33  thf(sk_E_type, type, sk_E: $i).
% 1.14/1.33  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.14/1.33  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.14/1.33  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.14/1.33  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.14/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.33  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.14/1.33  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.33  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.14/1.33  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.14/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.33  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.14/1.33  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.14/1.33  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.14/1.33  thf(sk_D_type, type, sk_D: $i).
% 1.14/1.33  thf(sk_G_type, type, sk_G: $i).
% 1.14/1.33  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.14/1.33  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.14/1.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.14/1.33  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.14/1.33  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.14/1.33  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.14/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.33  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.14/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.33  thf(sk_F_type, type, sk_F: $i).
% 1.14/1.33  thf(t88_tmap_1, conjecture,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.14/1.33             ( l1_pre_topc @ B ) ) =>
% 1.14/1.33           ( ![C:$i]:
% 1.14/1.33             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.14/1.33               ( ![D:$i]:
% 1.14/1.33                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.14/1.33                   ( ![E:$i]:
% 1.14/1.33                     ( ( ( v1_funct_1 @ E ) & 
% 1.14/1.33                         ( v1_funct_2 @
% 1.14/1.33                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.14/1.33                         ( m1_subset_1 @
% 1.14/1.33                           E @ 
% 1.14/1.33                           ( k1_zfmisc_1 @
% 1.14/1.33                             ( k2_zfmisc_1 @
% 1.14/1.33                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.14/1.33                       ( ( ( g1_pre_topc @
% 1.14/1.33                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.14/1.33                           ( D ) ) =>
% 1.14/1.33                         ( ![F:$i]:
% 1.14/1.33                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.14/1.33                             ( ![G:$i]:
% 1.14/1.33                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.14/1.33                                 ( ( ( ( F ) = ( G ) ) & 
% 1.14/1.33                                     ( r1_tmap_1 @
% 1.14/1.33                                       C @ B @ 
% 1.14/1.33                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.14/1.33                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.14/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.33    (~( ![A:$i]:
% 1.14/1.33        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.14/1.33            ( l1_pre_topc @ A ) ) =>
% 1.14/1.33          ( ![B:$i]:
% 1.14/1.33            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.14/1.33                ( l1_pre_topc @ B ) ) =>
% 1.14/1.33              ( ![C:$i]:
% 1.14/1.33                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.14/1.33                  ( ![D:$i]:
% 1.14/1.33                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.14/1.33                      ( ![E:$i]:
% 1.14/1.33                        ( ( ( v1_funct_1 @ E ) & 
% 1.14/1.33                            ( v1_funct_2 @
% 1.14/1.33                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.14/1.33                            ( m1_subset_1 @
% 1.14/1.33                              E @ 
% 1.14/1.33                              ( k1_zfmisc_1 @
% 1.14/1.33                                ( k2_zfmisc_1 @
% 1.14/1.33                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.14/1.33                          ( ( ( g1_pre_topc @
% 1.14/1.33                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.14/1.33                              ( D ) ) =>
% 1.14/1.33                            ( ![F:$i]:
% 1.14/1.33                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.14/1.33                                ( ![G:$i]:
% 1.14/1.33                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.14/1.33                                    ( ( ( ( F ) = ( G ) ) & 
% 1.14/1.33                                        ( r1_tmap_1 @
% 1.14/1.33                                          C @ B @ 
% 1.14/1.33                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.14/1.33                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.14/1.33    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.14/1.33  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(d3_struct_0, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.14/1.33  thf('1', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.33  thf('2', plain,
% 1.14/1.33      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('3', plain,
% 1.14/1.33      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 1.14/1.33        | ~ (l1_struct_0 @ sk_C))),
% 1.14/1.33      inference('sup+', [status(thm)], ['1', '2'])).
% 1.14/1.33  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(dt_m1_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( l1_pre_topc @ A ) =>
% 1.14/1.33       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.14/1.33  thf('5', plain,
% 1.14/1.33      (![X7 : $i, X8 : $i]:
% 1.14/1.33         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.14/1.33  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.14/1.33      inference('sup-', [status(thm)], ['4', '5'])).
% 1.14/1.33  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('8', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf(dt_l1_pre_topc, axiom,
% 1.14/1.33    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.14/1.33  thf('9', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.14/1.33  thf('10', plain, ((l1_struct_0 @ sk_C)),
% 1.14/1.33      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.33  thf('11', plain,
% 1.14/1.33      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.33  thf(abstractness_v1_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( l1_pre_topc @ A ) =>
% 1.14/1.33       ( ( v1_pre_topc @ A ) =>
% 1.14/1.33         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.14/1.33  thf('12', plain,
% 1.14/1.33      (![X2 : $i]:
% 1.14/1.33         (~ (v1_pre_topc @ X2)
% 1.14/1.33          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.14/1.33          | ~ (l1_pre_topc @ X2))),
% 1.14/1.33      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.14/1.33  thf(dt_u1_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( l1_pre_topc @ A ) =>
% 1.14/1.33       ( m1_subset_1 @
% 1.14/1.33         ( u1_pre_topc @ A ) @ 
% 1.14/1.33         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.14/1.33  thf('13', plain,
% 1.14/1.33      (![X9 : $i]:
% 1.14/1.33         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 1.14/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 1.14/1.33          | ~ (l1_pre_topc @ X9))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.14/1.33  thf(free_g1_pre_topc, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.14/1.33       ( ![C:$i,D:$i]:
% 1.14/1.33         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.14/1.33           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.14/1.33  thf('14', plain,
% 1.14/1.33      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.14/1.33         (((g1_pre_topc @ X13 @ X14) != (g1_pre_topc @ X11 @ X12))
% 1.14/1.33          | ((X13) = (X11))
% 1.14/1.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 1.14/1.33      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.14/1.33  thf('15', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (~ (l1_pre_topc @ X0)
% 1.14/1.33          | ((u1_struct_0 @ X0) = (X1))
% 1.14/1.33          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.14/1.33              != (g1_pre_topc @ X1 @ X2)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['13', '14'])).
% 1.14/1.33  thf('16', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v1_pre_topc @ X0)
% 1.14/1.33          | ((u1_struct_0 @ X0) = (X2))
% 1.14/1.33          | ~ (l1_pre_topc @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['12', '15'])).
% 1.14/1.33  thf('17', plain,
% 1.14/1.33      (![X1 : $i, X2 : $i]:
% 1.14/1.33         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.14/1.33          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.14/1.33          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.14/1.33      inference('simplify', [status(thm)], ['16'])).
% 1.14/1.33  thf('18', plain,
% 1.14/1.33      ((~ (v1_pre_topc @ sk_D)
% 1.14/1.33        | ~ (l1_pre_topc @ 
% 1.14/1.33             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.14/1.33        | ((u1_struct_0 @ 
% 1.14/1.33            (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.14/1.33            = (k2_struct_0 @ sk_C)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['11', '17'])).
% 1.14/1.33  thf('19', plain,
% 1.14/1.33      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(fc6_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ( v1_pre_topc @
% 1.14/1.33           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.14/1.33         ( v2_pre_topc @
% 1.14/1.33           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.14/1.33  thf('20', plain,
% 1.14/1.33      (![X10 : $i]:
% 1.14/1.33         ((v1_pre_topc @ 
% 1.14/1.33           (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 1.14/1.33          | ~ (l1_pre_topc @ X10)
% 1.14/1.33          | ~ (v2_pre_topc @ X10))),
% 1.14/1.33      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 1.14/1.33  thf('21', plain,
% 1.14/1.33      (((v1_pre_topc @ sk_D) | ~ (v2_pre_topc @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.14/1.33      inference('sup+', [status(thm)], ['19', '20'])).
% 1.14/1.33  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc1_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.14/1.33  thf('23', plain,
% 1.14/1.33      (![X3 : $i, X4 : $i]:
% 1.14/1.33         (~ (m1_pre_topc @ X3 @ X4)
% 1.14/1.33          | (v2_pre_topc @ X3)
% 1.14/1.33          | ~ (l1_pre_topc @ X4)
% 1.14/1.33          | ~ (v2_pre_topc @ X4))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.14/1.33  thf('24', plain,
% 1.14/1.33      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.14/1.33      inference('sup-', [status(thm)], ['22', '23'])).
% 1.14/1.33  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('27', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.33  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf('29', plain, ((v1_pre_topc @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['21', '27', '28'])).
% 1.14/1.33  thf('30', plain,
% 1.14/1.33      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.33  thf('31', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('32', plain,
% 1.14/1.33      (![X7 : $i, X8 : $i]:
% 1.14/1.33         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.14/1.33  thf('33', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.14/1.33      inference('sup-', [status(thm)], ['31', '32'])).
% 1.14/1.33  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('35', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.33  thf('36', plain,
% 1.14/1.33      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.33  thf('37', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.33  thf('38', plain,
% 1.14/1.33      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.14/1.33        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('39', plain, (((sk_F) = (sk_G))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('40', plain,
% 1.14/1.33      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.14/1.33        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.14/1.33      inference('demod', [status(thm)], ['38', '39'])).
% 1.14/1.33  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('42', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.33  thf('43', plain,
% 1.14/1.33      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('44', plain,
% 1.14/1.33      (![X1 : $i, X2 : $i]:
% 1.14/1.33         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.14/1.33          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.14/1.33          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.14/1.33      inference('simplify', [status(thm)], ['16'])).
% 1.14/1.33  thf('45', plain,
% 1.14/1.33      ((~ (v1_pre_topc @ sk_D)
% 1.14/1.33        | ~ (l1_pre_topc @ 
% 1.14/1.33             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.14/1.33        | ((u1_struct_0 @ 
% 1.14/1.33            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.14/1.33            = (u1_struct_0 @ sk_C)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['43', '44'])).
% 1.14/1.33  thf('46', plain, ((v1_pre_topc @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['21', '27', '28'])).
% 1.14/1.33  thf('47', plain,
% 1.14/1.33      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.33  thf('49', plain,
% 1.14/1.33      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('50', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 1.14/1.33  thf('51', plain,
% 1.14/1.33      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.14/1.33      inference('sup+', [status(thm)], ['42', '50'])).
% 1.14/1.33  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.33  thf('53', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.14/1.33  thf('54', plain, ((l1_struct_0 @ sk_D)),
% 1.14/1.33      inference('sup-', [status(thm)], ['52', '53'])).
% 1.14/1.33  thf('55', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['51', '54'])).
% 1.14/1.33  thf('56', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.33  thf('57', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.33  thf('58', plain,
% 1.14/1.33      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.14/1.33      inference('sup+', [status(thm)], ['56', '57'])).
% 1.14/1.33  thf('59', plain, ((l1_struct_0 @ sk_D)),
% 1.14/1.33      inference('sup-', [status(thm)], ['52', '53'])).
% 1.14/1.33  thf('60', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '59'])).
% 1.14/1.33  thf('61', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf(t2_tsep_1, axiom,
% 1.14/1.33    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.14/1.33  thf('62', plain,
% 1.14/1.33      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.14/1.33  thf(t65_pre_topc, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( l1_pre_topc @ A ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( l1_pre_topc @ B ) =>
% 1.14/1.33           ( ( m1_pre_topc @ A @ B ) <=>
% 1.14/1.33             ( m1_pre_topc @
% 1.14/1.33               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.14/1.33  thf('63', plain,
% 1.14/1.33      (![X21 : $i, X22 : $i]:
% 1.14/1.33         (~ (l1_pre_topc @ X21)
% 1.14/1.33          | ~ (m1_pre_topc @ X22 @ X21)
% 1.14/1.33          | (m1_pre_topc @ X22 @ 
% 1.14/1.33             (g1_pre_topc @ (u1_struct_0 @ X21) @ (u1_pre_topc @ X21)))
% 1.14/1.33          | ~ (l1_pre_topc @ X22))),
% 1.14/1.33      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.14/1.33  thf('64', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | (m1_pre_topc @ X0 @ 
% 1.14/1.33             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.14/1.33          | ~ (l1_pre_topc @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['62', '63'])).
% 1.14/1.33  thf('65', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((m1_pre_topc @ X0 @ 
% 1.14/1.33           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.14/1.33          | ~ (l1_pre_topc @ X0))),
% 1.14/1.33      inference('simplify', [status(thm)], ['64'])).
% 1.14/1.33  thf('66', plain,
% 1.14/1.33      (((m1_pre_topc @ sk_C @ 
% 1.14/1.33         (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.14/1.33        | ~ (l1_pre_topc @ sk_C))),
% 1.14/1.33      inference('sup+', [status(thm)], ['61', '65'])).
% 1.14/1.33  thf('67', plain,
% 1.14/1.33      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.33      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.33  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.14/1.33      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.14/1.33  thf('70', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_E @ 
% 1.14/1.33        (k1_zfmisc_1 @ 
% 1.14/1.33         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('71', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 1.14/1.33  thf('72', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_E @ 
% 1.14/1.33        (k1_zfmisc_1 @ 
% 1.14/1.33         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.33      inference('demod', [status(thm)], ['70', '71'])).
% 1.14/1.33  thf('73', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('74', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_E @ 
% 1.14/1.33        (k1_zfmisc_1 @ 
% 1.14/1.33         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.33      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.33  thf('75', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.33  thf(d5_tmap_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.14/1.33             ( l1_pre_topc @ B ) ) =>
% 1.14/1.33           ( ![C:$i]:
% 1.14/1.33             ( ( m1_pre_topc @ C @ A ) =>
% 1.14/1.33               ( ![D:$i]:
% 1.14/1.33                 ( ( m1_pre_topc @ D @ A ) =>
% 1.14/1.33                   ( ![E:$i]:
% 1.14/1.33                     ( ( ( v1_funct_1 @ E ) & 
% 1.14/1.33                         ( v1_funct_2 @
% 1.14/1.33                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.14/1.33                         ( m1_subset_1 @
% 1.14/1.33                           E @ 
% 1.14/1.33                           ( k1_zfmisc_1 @
% 1.14/1.33                             ( k2_zfmisc_1 @
% 1.14/1.33                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.14/1.33                       ( ( m1_pre_topc @ D @ C ) =>
% 1.14/1.33                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.14/1.33                           ( k2_partfun1 @
% 1.14/1.33                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.14/1.33                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.14/1.33  thf('76', plain,
% 1.14/1.33      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X28)
% 1.14/1.33          | ~ (v2_pre_topc @ X28)
% 1.14/1.33          | ~ (l1_pre_topc @ X28)
% 1.14/1.33          | ~ (m1_pre_topc @ X29 @ X30)
% 1.14/1.33          | ~ (m1_pre_topc @ X29 @ X31)
% 1.14/1.33          | ((k3_tmap_1 @ X30 @ X28 @ X31 @ X29 @ X32)
% 1.14/1.33              = (k2_partfun1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X28) @ 
% 1.14/1.33                 X32 @ (u1_struct_0 @ X29)))
% 1.14/1.33          | ~ (m1_subset_1 @ X32 @ 
% 1.14/1.33               (k1_zfmisc_1 @ 
% 1.14/1.33                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X28))))
% 1.14/1.33          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X28))
% 1.14/1.33          | ~ (v1_funct_1 @ X32)
% 1.14/1.33          | ~ (m1_pre_topc @ X31 @ X30)
% 1.14/1.33          | ~ (l1_pre_topc @ X30)
% 1.14/1.33          | ~ (v2_pre_topc @ X30)
% 1.14/1.33          | (v2_struct_0 @ X30))),
% 1.14/1.33      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.14/1.33  thf('77', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.33             (k1_zfmisc_1 @ 
% 1.14/1.33              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.33          | (v2_struct_0 @ X2)
% 1.14/1.33          | ~ (v2_pre_topc @ X2)
% 1.14/1.33          | ~ (l1_pre_topc @ X2)
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.14/1.33          | ~ (v1_funct_1 @ X1)
% 1.14/1.33          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.14/1.33          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 1.14/1.33              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 1.14/1.33                 X1 @ (u1_struct_0 @ X3)))
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ X2)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['75', '76'])).
% 1.14/1.33  thf('78', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.33  thf('79', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.33  thf('80', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.33             (k1_zfmisc_1 @ 
% 1.14/1.33              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.33          | (v2_struct_0 @ X2)
% 1.14/1.33          | ~ (v2_pre_topc @ X2)
% 1.14/1.33          | ~ (l1_pre_topc @ X2)
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.14/1.33          | ~ (v1_funct_1 @ X1)
% 1.14/1.33          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.14/1.33          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 1.14/1.33              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 1.14/1.33                 X1 @ (u1_struct_0 @ X3)))
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ X2)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.14/1.33  thf('81', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.33          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ X0)
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.14/1.33          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.14/1.33              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33                 sk_E @ (u1_struct_0 @ X1)))
% 1.14/1.33          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.33          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['74', '80'])).
% 1.14/1.33  thf('82', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('84', plain,
% 1.14/1.33      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('85', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 1.14/1.33  thf('86', plain,
% 1.14/1.33      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['84', '85'])).
% 1.14/1.33  thf('87', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('88', plain,
% 1.14/1.33      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.33  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('90', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ X0)
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.14/1.33          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.14/1.33              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33                 sk_E @ (u1_struct_0 @ X1)))
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['81', '82', '83', '88', '89'])).
% 1.14/1.33  thf('91', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.14/1.33          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33                 sk_E @ (u1_struct_0 @ sk_C)))
% 1.14/1.33          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.14/1.33          | (v2_struct_0 @ sk_B))),
% 1.14/1.33      inference('sup-', [status(thm)], ['69', '90'])).
% 1.14/1.33  thf('92', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('93', plain,
% 1.14/1.33      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.14/1.33  thf('94', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_E @ 
% 1.14/1.33        (k1_zfmisc_1 @ 
% 1.14/1.33         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.33      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.33  thf('95', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.33  thf(d4_tmap_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.14/1.33             ( l1_pre_topc @ B ) ) =>
% 1.14/1.33           ( ![C:$i]:
% 1.14/1.33             ( ( ( v1_funct_1 @ C ) & 
% 1.14/1.33                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.14/1.33                 ( m1_subset_1 @
% 1.14/1.33                   C @ 
% 1.14/1.33                   ( k1_zfmisc_1 @
% 1.14/1.33                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.14/1.33               ( ![D:$i]:
% 1.14/1.33                 ( ( m1_pre_topc @ D @ A ) =>
% 1.14/1.33                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.14/1.33                     ( k2_partfun1 @
% 1.14/1.33                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.14/1.33                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.14/1.33  thf('96', plain,
% 1.14/1.33      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X24)
% 1.14/1.33          | ~ (v2_pre_topc @ X24)
% 1.14/1.33          | ~ (l1_pre_topc @ X24)
% 1.14/1.33          | ~ (m1_pre_topc @ X25 @ X26)
% 1.14/1.33          | ((k2_tmap_1 @ X26 @ X24 @ X27 @ X25)
% 1.14/1.33              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24) @ 
% 1.14/1.33                 X27 @ (u1_struct_0 @ X25)))
% 1.14/1.33          | ~ (m1_subset_1 @ X27 @ 
% 1.14/1.33               (k1_zfmisc_1 @ 
% 1.14/1.33                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))))
% 1.14/1.33          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))
% 1.14/1.33          | ~ (v1_funct_1 @ X27)
% 1.14/1.33          | ~ (l1_pre_topc @ X26)
% 1.14/1.33          | ~ (v2_pre_topc @ X26)
% 1.14/1.33          | (v2_struct_0 @ X26))),
% 1.14/1.33      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.14/1.33  thf('97', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X2 @ 
% 1.14/1.33             (k1_zfmisc_1 @ 
% 1.14/1.33              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.14/1.33          | ~ (l1_struct_0 @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (v1_funct_1 @ X2)
% 1.14/1.33          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.14/1.33          | ((k2_tmap_1 @ X0 @ X1 @ X2 @ X3)
% 1.14/1.33              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 1.14/1.33                 (u1_struct_0 @ X3)))
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X1)
% 1.14/1.33          | ~ (v2_pre_topc @ X1)
% 1.14/1.33          | (v2_struct_0 @ X1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['95', '96'])).
% 1.14/1.33  thf('98', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.33          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.33          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.33          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.33              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33                 sk_E @ (u1_struct_0 @ X0)))
% 1.14/1.33          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.33          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.33          | ~ (l1_pre_topc @ sk_C)
% 1.14/1.33          | ~ (v2_pre_topc @ sk_C)
% 1.14/1.33          | (v2_struct_0 @ sk_C)
% 1.14/1.33          | ~ (l1_struct_0 @ sk_C))),
% 1.14/1.33      inference('sup-', [status(thm)], ['94', '97'])).
% 1.14/1.33  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('101', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('102', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('103', plain,
% 1.14/1.33      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.33  thf('104', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf('106', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.33  thf('107', plain, ((l1_struct_0 @ sk_C)),
% 1.14/1.33      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.33  thf('108', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.33          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.33              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33                 sk_E @ (u1_struct_0 @ X0)))
% 1.14/1.33          | (v2_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)],
% 1.14/1.33                ['98', '99', '100', '101', '102', '103', '104', '105', '106', 
% 1.14/1.33                 '107'])).
% 1.14/1.33  thf('109', plain,
% 1.14/1.33      ((~ (l1_pre_topc @ sk_C)
% 1.14/1.33        | (v2_struct_0 @ sk_C)
% 1.14/1.33        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.33            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33               sk_E @ (u1_struct_0 @ sk_C)))
% 1.14/1.33        | (v2_struct_0 @ sk_B))),
% 1.14/1.33      inference('sup-', [status(thm)], ['93', '108'])).
% 1.14/1.33  thf('110', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf('111', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('112', plain,
% 1.14/1.33      (((v2_struct_0 @ sk_C)
% 1.14/1.33        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.33            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33               sk_E @ (k2_struct_0 @ sk_C)))
% 1.14/1.33        | (v2_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.14/1.33  thf('113', plain, (~ (v2_struct_0 @ sk_C)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('114', plain,
% 1.14/1.33      (((v2_struct_0 @ sk_B)
% 1.14/1.33        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.33            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.33               sk_E @ (k2_struct_0 @ sk_C))))),
% 1.14/1.33      inference('clc', [status(thm)], ['112', '113'])).
% 1.14/1.33  thf('115', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('116', plain,
% 1.14/1.33      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.33         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.14/1.33            (k2_struct_0 @ sk_C)))),
% 1.14/1.33      inference('clc', [status(thm)], ['114', '115'])).
% 1.14/1.33  thf('117', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.14/1.33          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33              = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 1.14/1.33          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.14/1.33          | (v2_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['91', '92', '116'])).
% 1.14/1.33  thf('118', plain,
% 1.14/1.33      (((v2_struct_0 @ sk_B)
% 1.14/1.33        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.14/1.33        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 1.14/1.33        | ~ (l1_pre_topc @ sk_A)
% 1.14/1.33        | ~ (v2_pre_topc @ sk_A)
% 1.14/1.33        | (v2_struct_0 @ sk_A))),
% 1.14/1.33      inference('sup-', [status(thm)], ['41', '117'])).
% 1.14/1.33  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('122', plain,
% 1.14/1.33      (((v2_struct_0 @ sk_B)
% 1.14/1.33        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 1.14/1.33        | (v2_struct_0 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 1.14/1.33  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('124', plain,
% 1.14/1.33      (((v2_struct_0 @ sk_A)
% 1.14/1.33        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 1.14/1.33      inference('clc', [status(thm)], ['122', '123'])).
% 1.14/1.33  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('126', plain,
% 1.14/1.33      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.14/1.33         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 1.14/1.33      inference('clc', [status(thm)], ['124', '125'])).
% 1.14/1.33  thf('127', plain,
% 1.14/1.33      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 1.14/1.33        sk_F)),
% 1.14/1.33      inference('demod', [status(thm)], ['40', '126'])).
% 1.14/1.33  thf('128', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_E @ 
% 1.14/1.33        (k1_zfmisc_1 @ 
% 1.14/1.33         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.33      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.33  thf('129', plain,
% 1.14/1.33      (![X5 : $i]:
% 1.14/1.33         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.33      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.33  thf(t67_tmap_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.14/1.33             ( l1_pre_topc @ B ) ) =>
% 1.14/1.33           ( ![C:$i]:
% 1.14/1.33             ( ( ( v1_funct_1 @ C ) & 
% 1.14/1.33                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.14/1.33                 ( m1_subset_1 @
% 1.14/1.33                   C @ 
% 1.14/1.33                   ( k1_zfmisc_1 @
% 1.14/1.33                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.14/1.33               ( ![D:$i]:
% 1.14/1.33                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 1.14/1.33                     ( m1_pre_topc @ D @ B ) ) =>
% 1.14/1.33                   ( ![E:$i]:
% 1.14/1.33                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.14/1.33                       ( ![F:$i]:
% 1.14/1.33                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.14/1.33                           ( ( ( E ) = ( F ) ) =>
% 1.14/1.33                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 1.14/1.33                               ( r1_tmap_1 @
% 1.14/1.33                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.14/1.33  thf('130', plain,
% 1.14/1.33      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X39)
% 1.14/1.33          | ~ (v2_pre_topc @ X39)
% 1.14/1.33          | ~ (l1_pre_topc @ X39)
% 1.14/1.33          | (v2_struct_0 @ X40)
% 1.14/1.33          | ~ (v1_tsep_1 @ X40 @ X39)
% 1.14/1.33          | ~ (m1_pre_topc @ X40 @ X39)
% 1.14/1.33          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 1.14/1.33          | ~ (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ 
% 1.14/1.33               X41)
% 1.14/1.33          | (r1_tmap_1 @ X39 @ X42 @ X43 @ X44)
% 1.14/1.33          | ((X44) != (X41))
% 1.14/1.33          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X39))
% 1.14/1.33          | ~ (m1_subset_1 @ X43 @ 
% 1.14/1.33               (k1_zfmisc_1 @ 
% 1.14/1.33                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 1.14/1.33          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 1.14/1.33          | ~ (v1_funct_1 @ X43)
% 1.14/1.33          | ~ (l1_pre_topc @ X42)
% 1.14/1.33          | ~ (v2_pre_topc @ X42)
% 1.14/1.33          | (v2_struct_0 @ X42))),
% 1.14/1.33      inference('cnf', [status(esa)], [t67_tmap_1])).
% 1.14/1.33  thf('131', plain,
% 1.14/1.33      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.14/1.33         ((v2_struct_0 @ X42)
% 1.14/1.33          | ~ (v2_pre_topc @ X42)
% 1.14/1.33          | ~ (l1_pre_topc @ X42)
% 1.14/1.33          | ~ (v1_funct_1 @ X43)
% 1.14/1.33          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 1.14/1.33          | ~ (m1_subset_1 @ X43 @ 
% 1.14/1.33               (k1_zfmisc_1 @ 
% 1.14/1.33                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 1.14/1.33          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 1.14/1.33          | (r1_tmap_1 @ X39 @ X42 @ X43 @ X41)
% 1.14/1.33          | ~ (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ 
% 1.14/1.33               X41)
% 1.14/1.33          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 1.14/1.33          | ~ (m1_pre_topc @ X40 @ X39)
% 1.14/1.33          | ~ (v1_tsep_1 @ X40 @ X39)
% 1.14/1.33          | (v2_struct_0 @ X40)
% 1.14/1.33          | ~ (l1_pre_topc @ X39)
% 1.14/1.33          | ~ (v2_pre_topc @ X39)
% 1.14/1.33          | (v2_struct_0 @ X39))),
% 1.14/1.33      inference('simplify', [status(thm)], ['130'])).
% 1.14/1.33  thf('132', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X2 @ 
% 1.14/1.33             (k1_zfmisc_1 @ 
% 1.14/1.33              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.14/1.33          | ~ (l1_struct_0 @ X0)
% 1.14/1.33          | (v2_struct_0 @ X0)
% 1.14/1.33          | ~ (v2_pre_topc @ X0)
% 1.14/1.33          | ~ (l1_pre_topc @ X0)
% 1.14/1.33          | (v2_struct_0 @ X3)
% 1.14/1.33          | ~ (v1_tsep_1 @ X3 @ X0)
% 1.14/1.33          | ~ (m1_pre_topc @ X3 @ X0)
% 1.14/1.33          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.14/1.33          | ~ (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 1.14/1.33          | (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 1.14/1.33          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 1.14/1.33          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.14/1.33          | ~ (v1_funct_1 @ X2)
% 1.14/1.33          | ~ (l1_pre_topc @ X1)
% 1.14/1.33          | ~ (v2_pre_topc @ X1)
% 1.14/1.33          | (v2_struct_0 @ X1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['129', '131'])).
% 1.14/1.33  thf('133', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.33          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.33          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.33          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 1.14/1.33          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.33          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 1.14/1.33               X0)
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.14/1.33          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.14/1.33          | (v2_struct_0 @ X1)
% 1.14/1.33          | ~ (l1_pre_topc @ sk_C)
% 1.14/1.33          | ~ (v2_pre_topc @ sk_C)
% 1.14/1.33          | (v2_struct_0 @ sk_C)
% 1.14/1.33          | ~ (l1_struct_0 @ sk_C))),
% 1.14/1.33      inference('sup-', [status(thm)], ['128', '132'])).
% 1.14/1.33  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('136', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('137', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('138', plain,
% 1.14/1.33      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.33      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.33  thf('139', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.33      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.33  thf('140', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.33  thf('141', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.33  thf('142', plain, ((l1_struct_0 @ sk_C)),
% 1.14/1.33      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.33  thf('143', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         ((v2_struct_0 @ sk_B)
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.33          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.33          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 1.14/1.33               X0)
% 1.14/1.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.33          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.14/1.34          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ X1)
% 1.14/1.34          | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)],
% 1.14/1.34                ['133', '134', '135', '136', '137', '138', '139', '140', 
% 1.14/1.34                 '141', '142'])).
% 1.14/1.34  thf('144', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | (v2_struct_0 @ sk_C)
% 1.14/1.34        | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 1.14/1.34        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.14/1.34        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.14/1.34        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['127', '143'])).
% 1.14/1.34  thf('145', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf(dt_k2_subset_1, axiom,
% 1.14/1.34    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.14/1.34  thf('146', plain,
% 1.14/1.34      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 1.14/1.34      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.14/1.34  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.14/1.34  thf('147', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 1.14/1.34      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.14/1.34  thf('148', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.14/1.34      inference('demod', [status(thm)], ['146', '147'])).
% 1.14/1.34  thf(t16_tsep_1, axiom,
% 1.14/1.34    (![A:$i]:
% 1.14/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.34       ( ![B:$i]:
% 1.14/1.34         ( ( m1_pre_topc @ B @ A ) =>
% 1.14/1.34           ( ![C:$i]:
% 1.14/1.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.14/1.34               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.14/1.34                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.14/1.34                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.14/1.34  thf('149', plain,
% 1.14/1.34      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X33 @ X34)
% 1.14/1.34          | ((X35) != (u1_struct_0 @ X33))
% 1.14/1.34          | ~ (v3_pre_topc @ X35 @ X34)
% 1.14/1.34          | (v1_tsep_1 @ X33 @ X34)
% 1.14/1.34          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.14/1.34          | ~ (l1_pre_topc @ X34)
% 1.14/1.34          | ~ (v2_pre_topc @ X34))),
% 1.14/1.34      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.14/1.34  thf('150', plain,
% 1.14/1.34      (![X33 : $i, X34 : $i]:
% 1.14/1.34         (~ (v2_pre_topc @ X34)
% 1.14/1.34          | ~ (l1_pre_topc @ X34)
% 1.14/1.34          | ~ (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 1.14/1.34               (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.14/1.34          | (v1_tsep_1 @ X33 @ X34)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X33) @ X34)
% 1.14/1.34          | ~ (m1_pre_topc @ X33 @ X34))),
% 1.14/1.34      inference('simplify', [status(thm)], ['149'])).
% 1.14/1.34  thf('151', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X0 @ X0)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.14/1.34          | (v1_tsep_1 @ X0 @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['148', '150'])).
% 1.14/1.34  thf('152', plain,
% 1.14/1.34      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 1.14/1.34        | ~ (v2_pre_topc @ sk_C)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_C)
% 1.14/1.34        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.14/1.34        | ~ (m1_pre_topc @ sk_C @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['145', '151'])).
% 1.14/1.34  thf('153', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.14/1.34      inference('demod', [status(thm)], ['146', '147'])).
% 1.14/1.34  thf('154', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf(t60_pre_topc, axiom,
% 1.14/1.34    (![A:$i]:
% 1.14/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.34       ( ![B:$i]:
% 1.14/1.34         ( ( ( v3_pre_topc @ B @ A ) & 
% 1.14/1.34             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 1.14/1.34           ( ( v3_pre_topc @
% 1.14/1.34               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.14/1.34             ( m1_subset_1 @
% 1.14/1.34               B @ 
% 1.14/1.34               ( k1_zfmisc_1 @
% 1.14/1.34                 ( u1_struct_0 @
% 1.14/1.34                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 1.14/1.34  thf('155', plain,
% 1.14/1.34      (![X18 : $i, X19 : $i]:
% 1.14/1.34         (~ (v3_pre_topc @ X18 @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 1.14/1.34          | ~ (m1_subset_1 @ X18 @ 
% 1.14/1.34               (k1_zfmisc_1 @ 
% 1.14/1.34                (u1_struct_0 @ 
% 1.14/1.34                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))))
% 1.14/1.34          | (v3_pre_topc @ X18 @ X19)
% 1.14/1.34          | ~ (l1_pre_topc @ X19)
% 1.14/1.34          | ~ (v2_pre_topc @ X19))),
% 1.14/1.34      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.14/1.34  thf('156', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X0 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (u1_struct_0 @ 
% 1.14/1.34               (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))))
% 1.14/1.34          | ~ (v2_pre_topc @ sk_C)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_C)
% 1.14/1.34          | (v3_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (v3_pre_topc @ X0 @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['154', '155'])).
% 1.14/1.34  thf('157', plain,
% 1.14/1.34      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.34      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.34  thf('158', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('159', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.34  thf('160', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('161', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf('162', plain,
% 1.14/1.34      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.34      inference('demod', [status(thm)], ['3', '10'])).
% 1.14/1.34  thf('163', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.14/1.34          | (v3_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (v3_pre_topc @ X0 @ sk_D))),
% 1.14/1.34      inference('demod', [status(thm)],
% 1.14/1.34                ['156', '157', '158', '159', '160', '161', '162'])).
% 1.14/1.34  thf('164', plain,
% 1.14/1.34      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 1.14/1.34        | (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['153', '163'])).
% 1.14/1.34  thf('165', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['58', '59'])).
% 1.14/1.34  thf(fc10_tops_1, axiom,
% 1.14/1.34    (![A:$i]:
% 1.14/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.14/1.34       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.14/1.34  thf('166', plain,
% 1.14/1.34      (![X23 : $i]:
% 1.14/1.34         ((v3_pre_topc @ (k2_struct_0 @ X23) @ X23)
% 1.14/1.34          | ~ (l1_pre_topc @ X23)
% 1.14/1.34          | ~ (v2_pre_topc @ X23))),
% 1.14/1.34      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.14/1.34  thf('167', plain,
% 1.14/1.34      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 1.14/1.34        | ~ (v2_pre_topc @ sk_D)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_D))),
% 1.14/1.34      inference('sup+', [status(thm)], ['165', '166'])).
% 1.14/1.34  thf('168', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('169', plain,
% 1.14/1.34      (![X3 : $i, X4 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X3 @ X4)
% 1.14/1.34          | (v2_pre_topc @ X3)
% 1.14/1.34          | ~ (l1_pre_topc @ X4)
% 1.14/1.34          | ~ (v2_pre_topc @ X4))),
% 1.14/1.34      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.14/1.34  thf('170', plain,
% 1.14/1.34      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.14/1.34      inference('sup-', [status(thm)], ['168', '169'])).
% 1.14/1.34  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('173', plain, ((v2_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.14/1.34  thf('174', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('175', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['167', '173', '174'])).
% 1.14/1.34  thf('176', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['164', '175'])).
% 1.14/1.34  thf('177', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.34  thf('178', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('179', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.14/1.34  thf('180', plain,
% 1.14/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('181', plain,
% 1.14/1.34      (![X21 : $i, X22 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X21)
% 1.14/1.34          | ~ (m1_pre_topc @ X22 @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X21) @ (u1_pre_topc @ X21)))
% 1.14/1.34          | (m1_pre_topc @ X22 @ X21)
% 1.14/1.34          | ~ (l1_pre_topc @ X22))),
% 1.14/1.34      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.14/1.34  thf('182', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['180', '181'])).
% 1.14/1.34  thf('183', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('184', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ X0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['182', '183'])).
% 1.14/1.34  thf('185', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['179', '184'])).
% 1.14/1.34  thf('186', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('187', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['185', '186'])).
% 1.14/1.34  thf('188', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['152', '176', '177', '178', '187'])).
% 1.14/1.34  thf('189', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['185', '186'])).
% 1.14/1.34  thf('190', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf('191', plain,
% 1.14/1.34      (![X5 : $i]:
% 1.14/1.34         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.34  thf('192', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('193', plain, (((sk_F) = (sk_G))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('194', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['192', '193'])).
% 1.14/1.34  thf('195', plain,
% 1.14/1.34      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 1.14/1.34      inference('sup+', [status(thm)], ['191', '194'])).
% 1.14/1.34  thf('196', plain, ((l1_struct_0 @ sk_C)),
% 1.14/1.34      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.34  thf('197', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['195', '196'])).
% 1.14/1.34  thf('198', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['195', '196'])).
% 1.14/1.34  thf('199', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | (v2_struct_0 @ sk_C)
% 1.14/1.34        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)],
% 1.14/1.34                ['144', '188', '189', '190', '197', '198'])).
% 1.14/1.34  thf('200', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_B)
% 1.14/1.34        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('simplify', [status(thm)], ['199'])).
% 1.14/1.34  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('202', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C) | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F))),
% 1.14/1.34      inference('clc', [status(thm)], ['200', '201'])).
% 1.14/1.34  thf('203', plain, (~ (v2_struct_0 @ sk_C)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('204', plain, ((r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)),
% 1.14/1.34      inference('clc', [status(thm)], ['202', '203'])).
% 1.14/1.34  thf('205', plain,
% 1.14/1.34      ((m1_subset_1 @ sk_E @ 
% 1.14/1.34        (k1_zfmisc_1 @ 
% 1.14/1.34         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.34      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.34  thf('206', plain,
% 1.14/1.34      (![X5 : $i]:
% 1.14/1.34         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.14/1.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.14/1.34  thf('207', plain,
% 1.14/1.34      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.14/1.34         ((v2_struct_0 @ X39)
% 1.14/1.34          | ~ (v2_pre_topc @ X39)
% 1.14/1.34          | ~ (l1_pre_topc @ X39)
% 1.14/1.34          | (v2_struct_0 @ X40)
% 1.14/1.34          | ~ (v1_tsep_1 @ X40 @ X39)
% 1.14/1.34          | ~ (m1_pre_topc @ X40 @ X39)
% 1.14/1.34          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 1.14/1.34          | ~ (r1_tmap_1 @ X39 @ X42 @ X43 @ X44)
% 1.14/1.34          | (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ X41)
% 1.14/1.34          | ((X44) != (X41))
% 1.14/1.34          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X39))
% 1.14/1.34          | ~ (m1_subset_1 @ X43 @ 
% 1.14/1.34               (k1_zfmisc_1 @ 
% 1.14/1.34                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 1.14/1.34          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 1.14/1.34          | ~ (v1_funct_1 @ X43)
% 1.14/1.34          | ~ (l1_pre_topc @ X42)
% 1.14/1.34          | ~ (v2_pre_topc @ X42)
% 1.14/1.34          | (v2_struct_0 @ X42))),
% 1.14/1.34      inference('cnf', [status(esa)], [t67_tmap_1])).
% 1.14/1.34  thf('208', plain,
% 1.14/1.34      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.14/1.34         ((v2_struct_0 @ X42)
% 1.14/1.34          | ~ (v2_pre_topc @ X42)
% 1.14/1.34          | ~ (l1_pre_topc @ X42)
% 1.14/1.34          | ~ (v1_funct_1 @ X43)
% 1.14/1.34          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 1.14/1.34          | ~ (m1_subset_1 @ X43 @ 
% 1.14/1.34               (k1_zfmisc_1 @ 
% 1.14/1.34                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 1.14/1.34          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 1.14/1.34          | (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ X41)
% 1.14/1.34          | ~ (r1_tmap_1 @ X39 @ X42 @ X43 @ X41)
% 1.14/1.34          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 1.14/1.34          | ~ (m1_pre_topc @ X40 @ X39)
% 1.14/1.34          | ~ (v1_tsep_1 @ X40 @ X39)
% 1.14/1.34          | (v2_struct_0 @ X40)
% 1.14/1.34          | ~ (l1_pre_topc @ X39)
% 1.14/1.34          | ~ (v2_pre_topc @ X39)
% 1.14/1.34          | (v2_struct_0 @ X39))),
% 1.14/1.34      inference('simplify', [status(thm)], ['207'])).
% 1.14/1.34  thf('209', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X2 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.14/1.34          | ~ (l1_struct_0 @ X0)
% 1.14/1.34          | (v2_struct_0 @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | (v2_struct_0 @ X3)
% 1.14/1.34          | ~ (v1_tsep_1 @ X3 @ X0)
% 1.14/1.34          | ~ (m1_pre_topc @ X3 @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.14/1.34          | ~ (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 1.14/1.34          | (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 1.14/1.34          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 1.14/1.34          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.14/1.34          | ~ (v1_funct_1 @ X2)
% 1.14/1.34          | ~ (l1_pre_topc @ X1)
% 1.14/1.34          | ~ (v2_pre_topc @ X1)
% 1.14/1.34          | (v2_struct_0 @ X1))),
% 1.14/1.34      inference('sup-', [status(thm)], ['206', '208'])).
% 1.14/1.34  thf('210', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.34          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.34          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 1.14/1.34          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 1.14/1.34          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.34          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.14/1.34          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ X1)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_C)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ sk_C)
% 1.14/1.34          | ~ (l1_struct_0 @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['205', '209'])).
% 1.14/1.34  thf('211', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('213', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('214', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf('215', plain,
% 1.14/1.34      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.34  thf('216', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf('217', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('218', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.34  thf('219', plain, ((l1_struct_0 @ sk_C)),
% 1.14/1.34      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.34  thf('220', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 1.14/1.34          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.34          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.14/1.34          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ X1)
% 1.14/1.34          | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)],
% 1.14/1.34                ['210', '211', '212', '213', '214', '215', '216', '217', 
% 1.14/1.34                 '218', '219'])).
% 1.14/1.34  thf('221', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ X0)
% 1.14/1.34          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 1.14/1.34          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 1.14/1.34             sk_F)
% 1.14/1.34          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['204', '220'])).
% 1.14/1.34  thf('222', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['195', '196'])).
% 1.14/1.34  thf('223', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_C)
% 1.14/1.34          | (v2_struct_0 @ X0)
% 1.14/1.34          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 1.14/1.34          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 1.14/1.34             sk_F)
% 1.14/1.34          | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['221', '222'])).
% 1.14/1.34  thf('224', plain,
% 1.14/1.34      ((~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.14/1.34        | (v2_struct_0 @ sk_B)
% 1.14/1.34        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 1.14/1.34           sk_F)
% 1.14/1.34        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 1.14/1.34        | ~ (v1_tsep_1 @ sk_D @ sk_C)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['37', '223'])).
% 1.14/1.34  thf('225', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['195', '196'])).
% 1.14/1.34  thf('226', plain,
% 1.14/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('227', plain,
% 1.14/1.34      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 1.14/1.34      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.14/1.34  thf('228', plain,
% 1.14/1.34      (![X21 : $i, X22 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X21)
% 1.14/1.34          | ~ (m1_pre_topc @ X22 @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X21) @ (u1_pre_topc @ X21)))
% 1.14/1.34          | (m1_pre_topc @ X22 @ X21)
% 1.14/1.34          | ~ (l1_pre_topc @ X22))),
% 1.14/1.34      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.14/1.34  thf('229', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.14/1.34          | ~ (l1_pre_topc @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.14/1.34          | (m1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['227', '228'])).
% 1.14/1.34  thf('230', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.14/1.34      inference('simplify', [status(thm)], ['229'])).
% 1.14/1.34  thf('231', plain,
% 1.14/1.34      ((~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | (m1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['226', '230'])).
% 1.14/1.34  thf('232', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('233', plain,
% 1.14/1.34      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('234', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('235', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 1.14/1.34  thf('236', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.14/1.34              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34                 sk_E @ (u1_struct_0 @ X0)))
% 1.14/1.34          | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)],
% 1.14/1.34                ['98', '99', '100', '101', '102', '103', '104', '105', '106', 
% 1.14/1.34                 '107'])).
% 1.14/1.34  thf('237', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34               sk_E @ (u1_struct_0 @ sk_D)))
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['235', '236'])).
% 1.14/1.34  thf('238', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('239', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34               sk_E @ (k2_struct_0 @ sk_C)))
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['237', '238'])).
% 1.14/1.34  thf('240', plain, (~ (v2_struct_0 @ sk_C)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('241', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_B)
% 1.14/1.34        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34               sk_E @ (k2_struct_0 @ sk_C))))),
% 1.14/1.34      inference('clc', [status(thm)], ['239', '240'])).
% 1.14/1.34  thf('242', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('243', plain,
% 1.14/1.34      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.14/1.34         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.14/1.34            (k2_struct_0 @ sk_C)))),
% 1.14/1.34      inference('clc', [status(thm)], ['241', '242'])).
% 1.14/1.34  thf('244', plain,
% 1.14/1.34      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.34         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.14/1.34            (k2_struct_0 @ sk_C)))),
% 1.14/1.34      inference('clc', [status(thm)], ['114', '115'])).
% 1.14/1.34  thf('245', plain,
% 1.14/1.34      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.34         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 1.14/1.34      inference('sup+', [status(thm)], ['243', '244'])).
% 1.14/1.34  thf('246', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 1.14/1.34  thf('247', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('248', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['55', '60'])).
% 1.14/1.34  thf('249', plain,
% 1.14/1.34      (![X33 : $i, X34 : $i]:
% 1.14/1.34         (~ (v2_pre_topc @ X34)
% 1.14/1.34          | ~ (l1_pre_topc @ X34)
% 1.14/1.34          | ~ (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 1.14/1.34               (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.14/1.34          | (v1_tsep_1 @ X33 @ X34)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X33) @ X34)
% 1.14/1.34          | ~ (m1_pre_topc @ X33 @ X34))),
% 1.14/1.34      inference('simplify', [status(thm)], ['149'])).
% 1.14/1.34  thf('250', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.14/1.34             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_C)
% 1.14/1.34          | (v1_tsep_1 @ X0 @ sk_C)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_C)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['248', '249'])).
% 1.14/1.34  thf('251', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('252', plain, ((v2_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.14/1.34  thf('253', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.14/1.34             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_C)
% 1.14/1.34          | (v1_tsep_1 @ X0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['250', '251', '252'])).
% 1.14/1.34  thf('254', plain,
% 1.14/1.34      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 1.14/1.34           (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.14/1.34        | (v1_tsep_1 @ sk_D @ sk_C)
% 1.14/1.34        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C)
% 1.14/1.34        | ~ (m1_pre_topc @ sk_D @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['247', '253'])).
% 1.14/1.34  thf('255', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.14/1.34      inference('demod', [status(thm)], ['146', '147'])).
% 1.14/1.34  thf('256', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('257', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['164', '175'])).
% 1.14/1.34  thf('258', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 1.14/1.34  thf('259', plain, ((v1_tsep_1 @ sk_D @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['254', '255', '256', '257', '258'])).
% 1.14/1.34  thf('260', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_B)
% 1.14/1.34        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 1.14/1.34           sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['224', '225', '245', '246', '259'])).
% 1.14/1.34  thf('261', plain,
% 1.14/1.34      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 1.14/1.34      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.14/1.34  thf('262', plain,
% 1.14/1.34      ((m1_subset_1 @ sk_E @ 
% 1.14/1.34        (k1_zfmisc_1 @ 
% 1.14/1.34         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.34      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.34  thf('263', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('264', plain,
% 1.14/1.34      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.14/1.34         ((v2_struct_0 @ X24)
% 1.14/1.34          | ~ (v2_pre_topc @ X24)
% 1.14/1.34          | ~ (l1_pre_topc @ X24)
% 1.14/1.34          | ~ (m1_pre_topc @ X25 @ X26)
% 1.14/1.34          | ((k2_tmap_1 @ X26 @ X24 @ X27 @ X25)
% 1.14/1.34              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24) @ 
% 1.14/1.34                 X27 @ (u1_struct_0 @ X25)))
% 1.14/1.34          | ~ (m1_subset_1 @ X27 @ 
% 1.14/1.34               (k1_zfmisc_1 @ 
% 1.14/1.34                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))))
% 1.14/1.34          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))
% 1.14/1.34          | ~ (v1_funct_1 @ X27)
% 1.14/1.34          | ~ (l1_pre_topc @ X26)
% 1.14/1.34          | ~ (v2_pre_topc @ X26)
% 1.14/1.34          | (v2_struct_0 @ X26))),
% 1.14/1.34      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.14/1.34  thf('265', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_D)
% 1.14/1.34          | ~ (v1_funct_1 @ X1)
% 1.14/1.34          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.14/1.34          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 1.14/1.34              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 1.14/1.34                 X1 @ (u1_struct_0 @ X2)))
% 1.14/1.34          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0)
% 1.14/1.34          | (v2_struct_0 @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['263', '264'])).
% 1.14/1.34  thf('266', plain, ((v2_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.14/1.34  thf('267', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('268', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('269', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('270', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (v1_funct_1 @ X1)
% 1.14/1.34          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.14/1.34          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 1.14/1.34              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 1.14/1.34                 X1 @ (u1_struct_0 @ X2)))
% 1.14/1.34          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0)
% 1.14/1.34          | (v2_struct_0 @ X0))),
% 1.14/1.34      inference('demod', [status(thm)], ['265', '266', '267', '268', '269'])).
% 1.14/1.34  thf('271', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.14/1.34          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34                 sk_E @ (u1_struct_0 @ X0)))
% 1.14/1.34          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.34          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.34          | (v2_struct_0 @ sk_D))),
% 1.14/1.34      inference('sup-', [status(thm)], ['262', '270'])).
% 1.14/1.34  thf('272', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('273', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('274', plain,
% 1.14/1.34      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.34  thf('275', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('276', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.14/1.34          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34                 sk_E @ (u1_struct_0 @ X0)))
% 1.14/1.34          | (v2_struct_0 @ sk_D))),
% 1.14/1.34      inference('demod', [status(thm)], ['271', '272', '273', '274', '275'])).
% 1.14/1.34  thf('277', plain,
% 1.14/1.34      ((~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.14/1.34               sk_E @ (u1_struct_0 @ sk_D)))
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['261', '276'])).
% 1.14/1.34  thf('278', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('279', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('280', plain,
% 1.14/1.34      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.14/1.34         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.14/1.34            (k2_struct_0 @ sk_C)))),
% 1.14/1.34      inference('clc', [status(thm)], ['114', '115'])).
% 1.14/1.34  thf('281', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_D)
% 1.14/1.34        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['277', '278', '279', '280'])).
% 1.14/1.34  thf('282', plain, (~ (v2_struct_0 @ sk_D)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('283', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_B)
% 1.14/1.34        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.14/1.34            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 1.14/1.34      inference('clc', [status(thm)], ['281', '282'])).
% 1.14/1.34  thf('284', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('285', plain,
% 1.14/1.34      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.14/1.34         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 1.14/1.34      inference('clc', [status(thm)], ['283', '284'])).
% 1.14/1.34  thf('286', plain,
% 1.14/1.34      ((m1_subset_1 @ sk_E @ 
% 1.14/1.34        (k1_zfmisc_1 @ 
% 1.14/1.34         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.14/1.34      inference('demod', [status(thm)], ['72', '73'])).
% 1.14/1.34  thf('287', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('288', plain,
% 1.14/1.34      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.14/1.34         ((v2_struct_0 @ X42)
% 1.14/1.34          | ~ (v2_pre_topc @ X42)
% 1.14/1.34          | ~ (l1_pre_topc @ X42)
% 1.14/1.34          | ~ (v1_funct_1 @ X43)
% 1.14/1.34          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 1.14/1.34          | ~ (m1_subset_1 @ X43 @ 
% 1.14/1.34               (k1_zfmisc_1 @ 
% 1.14/1.34                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 1.14/1.34          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 1.14/1.34          | (r1_tmap_1 @ X39 @ X42 @ X43 @ X41)
% 1.14/1.34          | ~ (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ 
% 1.14/1.34               X41)
% 1.14/1.34          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 1.14/1.34          | ~ (m1_pre_topc @ X40 @ X39)
% 1.14/1.34          | ~ (v1_tsep_1 @ X40 @ X39)
% 1.14/1.34          | (v2_struct_0 @ X40)
% 1.14/1.34          | ~ (l1_pre_topc @ X39)
% 1.14/1.34          | ~ (v2_pre_topc @ X39)
% 1.14/1.34          | (v2_struct_0 @ X39))),
% 1.14/1.34      inference('simplify', [status(thm)], ['130'])).
% 1.14/1.34  thf('289', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ X2)
% 1.14/1.34          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 1.14/1.34          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.14/1.34          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.14/1.34          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 1.14/1.34          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 1.14/1.34          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.14/1.34          | ~ (v1_funct_1 @ X1)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0)
% 1.14/1.34          | (v2_struct_0 @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['287', '288'])).
% 1.14/1.34  thf('290', plain, ((v2_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.14/1.34  thf('291', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('292', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('293', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('294', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.34         (~ (m1_subset_1 @ X1 @ 
% 1.14/1.34             (k1_zfmisc_1 @ 
% 1.14/1.34              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ X2)
% 1.14/1.34          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 1.14/1.34          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.14/1.34          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.14/1.34          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 1.14/1.34          | ~ (m1_subset_1 @ X3 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.14/1.34          | ~ (v1_funct_1 @ X1)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0)
% 1.14/1.34          | (v2_struct_0 @ X0))),
% 1.14/1.34      inference('demod', [status(thm)], ['289', '290', '291', '292', '293'])).
% 1.14/1.34  thf('295', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (v2_pre_topc @ sk_B)
% 1.14/1.34          | ~ (l1_pre_topc @ sk_B)
% 1.14/1.34          | ~ (v1_funct_1 @ sk_E)
% 1.14/1.34          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 1.14/1.34               X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.34          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.14/1.34          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ X1)
% 1.14/1.34          | (v2_struct_0 @ sk_D))),
% 1.14/1.34      inference('sup-', [status(thm)], ['286', '294'])).
% 1.14/1.34  thf('296', plain, ((v2_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('297', plain, ((l1_pre_topc @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('298', plain, ((v1_funct_1 @ sk_E)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('299', plain,
% 1.14/1.34      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.34  thf('300', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 1.14/1.34               X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.14/1.34          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.14/1.34          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ X1)
% 1.14/1.34          | (v2_struct_0 @ sk_D))),
% 1.14/1.34      inference('demod', [status(thm)], ['295', '296', '297', '298', '299'])).
% 1.14/1.34  thf('301', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.14/1.34             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 1.14/1.34          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['285', '300'])).
% 1.14/1.34  thf('302', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('303', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X0 @ X0)
% 1.14/1.34          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.14/1.34          | (v1_tsep_1 @ X0 @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v2_pre_topc @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['148', '150'])).
% 1.14/1.34  thf('304', plain,
% 1.14/1.34      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 1.14/1.34        | ~ (v2_pre_topc @ sk_D)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | (v1_tsep_1 @ sk_D @ sk_D)
% 1.14/1.34        | ~ (m1_pre_topc @ sk_D @ sk_D))),
% 1.14/1.34      inference('sup-', [status(thm)], ['302', '303'])).
% 1.14/1.34  thf('305', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['167', '173', '174'])).
% 1.14/1.34  thf('306', plain, ((v2_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.14/1.34  thf('307', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('308', plain,
% 1.14/1.34      (![X2 : $i]:
% 1.14/1.34         (~ (v1_pre_topc @ X2)
% 1.14/1.34          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.14/1.34          | ~ (l1_pre_topc @ X2))),
% 1.14/1.34      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.14/1.34  thf('309', plain,
% 1.14/1.34      (![X2 : $i]:
% 1.14/1.34         (~ (v1_pre_topc @ X2)
% 1.14/1.34          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.14/1.34          | ~ (l1_pre_topc @ X2))),
% 1.14/1.34      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.14/1.34  thf('310', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.14/1.34      inference('simplify', [status(thm)], ['229'])).
% 1.14/1.34  thf('311', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['309', '310'])).
% 1.14/1.34  thf('312', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((m1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (v1_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0))),
% 1.14/1.34      inference('simplify', [status(thm)], ['311'])).
% 1.14/1.34  thf('313', plain,
% 1.14/1.34      (![X7 : $i, X8 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.14/1.34      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.14/1.34  thf('314', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X0)
% 1.14/1.34          | ~ (v1_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | (l1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['312', '313'])).
% 1.14/1.34  thf('315', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((l1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.14/1.34          | ~ (v1_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0))),
% 1.14/1.34      inference('simplify', [status(thm)], ['314'])).
% 1.14/1.34  thf('316', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((m1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (v1_pre_topc @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ X0))),
% 1.14/1.34      inference('simplify', [status(thm)], ['311'])).
% 1.14/1.34  thf('317', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.14/1.34          | ~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ X0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['182', '183'])).
% 1.14/1.34  thf('318', plain,
% 1.14/1.34      ((~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | ~ (v1_pre_topc @ sk_D)
% 1.14/1.34        | (m1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C)
% 1.14/1.34        | ~ (l1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['316', '317'])).
% 1.14/1.34  thf('319', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('320', plain, ((v1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['21', '27', '28'])).
% 1.14/1.34  thf('321', plain,
% 1.14/1.34      (((m1_pre_topc @ 
% 1.14/1.34         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C)
% 1.14/1.34        | ~ (l1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 1.14/1.34      inference('demod', [status(thm)], ['318', '319', '320'])).
% 1.14/1.34  thf('322', plain,
% 1.14/1.34      ((~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | ~ (v1_pre_topc @ sk_D)
% 1.14/1.34        | (m1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C))),
% 1.14/1.34      inference('sup-', [status(thm)], ['315', '321'])).
% 1.14/1.34  thf('323', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('324', plain, ((v1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['21', '27', '28'])).
% 1.14/1.34  thf('325', plain,
% 1.14/1.34      ((m1_pre_topc @ 
% 1.14/1.34        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['322', '323', '324'])).
% 1.14/1.34  thf('326', plain,
% 1.14/1.34      (![X7 : $i, X8 : $i]:
% 1.14/1.34         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.14/1.34      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.14/1.34  thf('327', plain,
% 1.14/1.34      ((~ (l1_pre_topc @ sk_C)
% 1.14/1.34        | (l1_pre_topc @ 
% 1.14/1.34           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['325', '326'])).
% 1.14/1.34  thf('328', plain, ((l1_pre_topc @ sk_C)),
% 1.14/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.34  thf('329', plain,
% 1.14/1.34      ((l1_pre_topc @ 
% 1.14/1.34        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 1.14/1.34      inference('demod', [status(thm)], ['327', '328'])).
% 1.14/1.34  thf('330', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (l1_pre_topc @ X0)
% 1.14/1.34          | (m1_pre_topc @ 
% 1.14/1.34             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.14/1.34          | ~ (l1_pre_topc @ 
% 1.14/1.34               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.14/1.34      inference('simplify', [status(thm)], ['229'])).
% 1.14/1.34  thf('331', plain,
% 1.14/1.34      (((m1_pre_topc @ 
% 1.14/1.34         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_D)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_D))),
% 1.14/1.34      inference('sup-', [status(thm)], ['329', '330'])).
% 1.14/1.34  thf('332', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('333', plain,
% 1.14/1.34      ((m1_pre_topc @ 
% 1.14/1.34        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['331', '332'])).
% 1.14/1.34  thf('334', plain,
% 1.14/1.34      (((m1_pre_topc @ sk_D @ sk_D)
% 1.14/1.34        | ~ (l1_pre_topc @ sk_D)
% 1.14/1.34        | ~ (v1_pre_topc @ sk_D))),
% 1.14/1.34      inference('sup+', [status(thm)], ['308', '333'])).
% 1.14/1.34  thf('335', plain, ((l1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.34  thf('336', plain, ((v1_pre_topc @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['21', '27', '28'])).
% 1.14/1.34  thf('337', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['334', '335', '336'])).
% 1.14/1.34  thf('338', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['304', '305', '306', '307', '337'])).
% 1.14/1.34  thf('339', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.14/1.34      inference('demod', [status(thm)], ['334', '335', '336'])).
% 1.14/1.34  thf('340', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['18', '29', '30', '35', '36'])).
% 1.14/1.34  thf('341', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.14/1.34             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['301', '338', '339', '340'])).
% 1.14/1.34  thf('342', plain,
% 1.14/1.34      (![X0 : $i]:
% 1.14/1.34         ((v2_struct_0 @ sk_B)
% 1.14/1.34          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.14/1.34          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.14/1.34          | (v2_struct_0 @ sk_D)
% 1.14/1.34          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.14/1.34               (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0))),
% 1.14/1.34      inference('simplify', [status(thm)], ['341'])).
% 1.14/1.34  thf('343', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_B)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.14/1.34        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['260', '342'])).
% 1.14/1.34  thf('344', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.14/1.34      inference('demod', [status(thm)], ['195', '196'])).
% 1.14/1.34  thf('345', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_B)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('demod', [status(thm)], ['343', '344'])).
% 1.14/1.34  thf('346', plain,
% 1.14/1.34      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.14/1.34        | (v2_struct_0 @ sk_B)
% 1.14/1.34        | (v2_struct_0 @ sk_D)
% 1.14/1.34        | (v2_struct_0 @ sk_C))),
% 1.14/1.34      inference('simplify', [status(thm)], ['345'])).
% 1.14/1.34  thf('347', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('348', plain,
% 1.14/1.34      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 1.14/1.34      inference('sup-', [status(thm)], ['346', '347'])).
% 1.14/1.34  thf('349', plain, (~ (v2_struct_0 @ sk_C)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('350', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 1.14/1.34      inference('clc', [status(thm)], ['348', '349'])).
% 1.14/1.34  thf('351', plain, (~ (v2_struct_0 @ sk_B)),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('352', plain, ((v2_struct_0 @ sk_D)),
% 1.14/1.34      inference('clc', [status(thm)], ['350', '351'])).
% 1.14/1.34  thf('353', plain, ($false), inference('demod', [status(thm)], ['0', '352'])).
% 1.14/1.34  
% 1.14/1.34  % SZS output end Refutation
% 1.14/1.34  
% 1.14/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
