%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e5NwlkD2W5

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:28 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  197 (1907 expanded)
%              Number of leaves         :   41 ( 575 expanded)
%              Depth                    :   21
%              Number of atoms          : 1710 (51049 expanded)
%              Number of equality atoms :   63 (1682 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( g1_pre_topc @ X11 @ X12 )
       != ( g1_pre_topc @ X9 @ X10 ) )
      | ( X11 = X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('15',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','31'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('49',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('51',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['43','46'])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('53',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['43','46'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['40','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','58'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf(t86_tmap_1,axiom,(
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
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_tsep_1 @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ( X30 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( v1_tsep_1 @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('73',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('80',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

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

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('89',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('92',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('93',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('94',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','97'])).

thf('99',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['86','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('104',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('105',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('106',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('108',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('109',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('111',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('112',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( X14
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('113',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) @ X16 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('116',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('118',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('120',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('122',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','125'])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['110','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('129',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['101','102','103','109','130'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('133',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('139',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('141',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('142',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','131','132','139','140','141','142','143','144'])).

thf('146',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['0','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e5NwlkD2W5
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.93/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.13  % Solved by: fo/fo7.sh
% 1.93/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.13  % done 2342 iterations in 1.650s
% 1.93/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.13  % SZS output start Refutation
% 1.93/2.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.93/2.13  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.93/2.13  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.13  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.93/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.93/2.13  thf(sk_E_type, type, sk_E: $i).
% 1.93/2.13  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.93/2.13  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.93/2.13  thf(sk_F_type, type, sk_F: $i).
% 1.93/2.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.93/2.13  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.93/2.13  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.93/2.13  thf(sk_D_type, type, sk_D: $i).
% 1.93/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.93/2.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.93/2.13  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.93/2.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.13  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.93/2.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.93/2.13  thf(sk_G_type, type, sk_G: $i).
% 1.93/2.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.93/2.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.93/2.13  thf(t88_tmap_1, conjecture,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.13             ( l1_pre_topc @ B ) ) =>
% 1.93/2.13           ( ![C:$i]:
% 1.93/2.13             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.13               ( ![D:$i]:
% 1.93/2.13                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.93/2.13                   ( ![E:$i]:
% 1.93/2.13                     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.13                         ( v1_funct_2 @
% 1.93/2.13                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.13                         ( m1_subset_1 @
% 1.93/2.13                           E @ 
% 1.93/2.13                           ( k1_zfmisc_1 @
% 1.93/2.13                             ( k2_zfmisc_1 @
% 1.93/2.13                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.13                       ( ( ( g1_pre_topc @
% 1.93/2.13                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.93/2.13                           ( D ) ) =>
% 1.93/2.13                         ( ![F:$i]:
% 1.93/2.13                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.93/2.13                             ( ![G:$i]:
% 1.93/2.13                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.93/2.13                                 ( ( ( ( F ) = ( G ) ) & 
% 1.93/2.13                                     ( r1_tmap_1 @
% 1.93/2.13                                       C @ B @ 
% 1.93/2.13                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.93/2.13                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.13    (~( ![A:$i]:
% 1.93/2.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.13            ( l1_pre_topc @ A ) ) =>
% 1.93/2.13          ( ![B:$i]:
% 1.93/2.13            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.13                ( l1_pre_topc @ B ) ) =>
% 1.93/2.13              ( ![C:$i]:
% 1.93/2.13                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.13                  ( ![D:$i]:
% 1.93/2.13                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.93/2.13                      ( ![E:$i]:
% 1.93/2.13                        ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.13                            ( v1_funct_2 @
% 1.93/2.13                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.13                            ( m1_subset_1 @
% 1.93/2.13                              E @ 
% 1.93/2.13                              ( k1_zfmisc_1 @
% 1.93/2.13                                ( k2_zfmisc_1 @
% 1.93/2.13                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.13                          ( ( ( g1_pre_topc @
% 1.93/2.13                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.93/2.13                              ( D ) ) =>
% 1.93/2.13                            ( ![F:$i]:
% 1.93/2.13                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.93/2.13                                ( ![G:$i]:
% 1.93/2.13                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.93/2.13                                    ( ( ( ( F ) = ( G ) ) & 
% 1.93/2.13                                        ( r1_tmap_1 @
% 1.93/2.13                                          C @ B @ 
% 1.93/2.13                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.93/2.13                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.93/2.13    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.93/2.13  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('1', plain,
% 1.93/2.13      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.93/2.13        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('2', plain, (((sk_F) = (sk_G))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('3', plain,
% 1.93/2.13      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.93/2.13        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.93/2.13      inference('demod', [status(thm)], ['1', '2'])).
% 1.93/2.13  thf('4', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_E @ 
% 1.93/2.13        (k1_zfmisc_1 @ 
% 1.93/2.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('5', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(abstractness_v1_pre_topc, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_pre_topc @ A ) =>
% 1.93/2.13       ( ( v1_pre_topc @ A ) =>
% 1.93/2.13         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.93/2.13  thf('6', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (v1_pre_topc @ X0)
% 1.93/2.13          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.93/2.13  thf(dt_u1_pre_topc, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_pre_topc @ A ) =>
% 1.93/2.13       ( m1_subset_1 @
% 1.93/2.13         ( u1_pre_topc @ A ) @ 
% 1.93/2.13         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.93/2.13  thf('7', plain,
% 1.93/2.13      (![X7 : $i]:
% 1.93/2.13         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 1.93/2.13           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 1.93/2.13          | ~ (l1_pre_topc @ X7))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.93/2.13  thf(free_g1_pre_topc, axiom,
% 1.93/2.13    (![A:$i,B:$i]:
% 1.93/2.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.93/2.13       ( ![C:$i,D:$i]:
% 1.93/2.13         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.93/2.13           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.93/2.13  thf('8', plain,
% 1.93/2.13      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.93/2.13         (((g1_pre_topc @ X11 @ X12) != (g1_pre_topc @ X9 @ X10))
% 1.93/2.13          | ((X11) = (X9))
% 1.93/2.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 1.93/2.13      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.93/2.13  thf('9', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         (~ (l1_pre_topc @ X0)
% 1.93/2.13          | ((u1_struct_0 @ X0) = (X1))
% 1.93/2.13          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.93/2.13              != (g1_pre_topc @ X1 @ X2)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['7', '8'])).
% 1.93/2.13  thf('10', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | ~ (v1_pre_topc @ X0)
% 1.93/2.13          | ((u1_struct_0 @ X0) = (X2))
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['6', '9'])).
% 1.93/2.13  thf('11', plain,
% 1.93/2.13      (![X1 : $i, X2 : $i]:
% 1.93/2.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.93/2.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.93/2.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.93/2.13      inference('simplify', [status(thm)], ['10'])).
% 1.93/2.13  thf('12', plain,
% 1.93/2.13      ((~ (v1_pre_topc @ sk_D)
% 1.93/2.13        | ~ (l1_pre_topc @ 
% 1.93/2.13             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.93/2.13        | ((u1_struct_0 @ 
% 1.93/2.13            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.93/2.13            = (u1_struct_0 @ sk_C)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['5', '11'])).
% 1.93/2.13  thf('13', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(fc7_pre_topc, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( ( ~( v2_struct_0 @
% 1.93/2.13              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 1.93/2.13         ( v1_pre_topc @
% 1.93/2.13           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.93/2.13  thf('14', plain,
% 1.93/2.13      (![X8 : $i]:
% 1.93/2.13         ((v1_pre_topc @ 
% 1.93/2.13           (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 1.93/2.13          | ~ (l1_pre_topc @ X8)
% 1.93/2.13          | (v2_struct_0 @ X8))),
% 1.93/2.13      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 1.93/2.13  thf('15', plain,
% 1.93/2.13      (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.93/2.13      inference('sup+', [status(thm)], ['13', '14'])).
% 1.93/2.13  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(dt_m1_pre_topc, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_pre_topc @ A ) =>
% 1.93/2.13       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.93/2.13  thf('17', plain,
% 1.93/2.13      (![X5 : $i, X6 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.13  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.93/2.13      inference('sup-', [status(thm)], ['16', '17'])).
% 1.93/2.13  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['18', '19'])).
% 1.93/2.13  thf('21', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['15', '20'])).
% 1.93/2.13  thf('22', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('23', plain, ((v1_pre_topc @ sk_D)),
% 1.93/2.13      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.13  thf('24', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('26', plain,
% 1.93/2.13      (![X5 : $i, X6 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.13  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.93/2.13      inference('sup-', [status(thm)], ['25', '26'])).
% 1.93/2.13  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('30', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('31', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 1.93/2.13  thf('32', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_E @ 
% 1.93/2.13        (k1_zfmisc_1 @ 
% 1.93/2.13         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.93/2.13      inference('demod', [status(thm)], ['4', '31'])).
% 1.93/2.13  thf(d3_struct_0, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.93/2.13  thf('33', plain,
% 1.93/2.13      (![X3 : $i]:
% 1.93/2.13         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.93/2.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.93/2.13  thf('34', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 1.93/2.13  thf('35', plain,
% 1.93/2.13      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.93/2.13      inference('sup+', [status(thm)], ['33', '34'])).
% 1.93/2.13  thf('36', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf(dt_l1_pre_topc, axiom,
% 1.93/2.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.93/2.13  thf('37', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.93/2.13  thf('38', plain, ((l1_struct_0 @ sk_D)),
% 1.93/2.13      inference('sup-', [status(thm)], ['36', '37'])).
% 1.93/2.13  thf('39', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['35', '38'])).
% 1.93/2.13  thf('40', plain,
% 1.93/2.13      (![X3 : $i]:
% 1.93/2.13         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.93/2.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.93/2.13  thf('41', plain,
% 1.93/2.13      (![X3 : $i]:
% 1.93/2.13         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.93/2.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.93/2.13  thf('42', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('43', plain,
% 1.93/2.13      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 1.93/2.13        | ~ (l1_struct_0 @ sk_C))),
% 1.93/2.13      inference('sup+', [status(thm)], ['41', '42'])).
% 1.93/2.13  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['18', '19'])).
% 1.93/2.13  thf('45', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.93/2.13  thf('46', plain, ((l1_struct_0 @ sk_C)),
% 1.93/2.13      inference('sup-', [status(thm)], ['44', '45'])).
% 1.93/2.13  thf('47', plain,
% 1.93/2.13      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['43', '46'])).
% 1.93/2.13  thf('48', plain,
% 1.93/2.13      (![X1 : $i, X2 : $i]:
% 1.93/2.13         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.93/2.13          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.93/2.13          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.93/2.13      inference('simplify', [status(thm)], ['10'])).
% 1.93/2.13  thf('49', plain,
% 1.93/2.13      ((~ (v1_pre_topc @ sk_D)
% 1.93/2.13        | ~ (l1_pre_topc @ 
% 1.93/2.13             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.93/2.13        | ((u1_struct_0 @ 
% 1.93/2.13            (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.93/2.13            = (k2_struct_0 @ sk_C)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['47', '48'])).
% 1.93/2.13  thf('50', plain, ((v1_pre_topc @ sk_D)),
% 1.93/2.13      inference('clc', [status(thm)], ['21', '22'])).
% 1.93/2.13  thf('51', plain,
% 1.93/2.13      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['43', '46'])).
% 1.93/2.13  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('53', plain,
% 1.93/2.13      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['43', '46'])).
% 1.93/2.13  thf('54', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.93/2.13  thf('55', plain,
% 1.93/2.13      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 1.93/2.13      inference('sup+', [status(thm)], ['40', '54'])).
% 1.93/2.13  thf('56', plain, ((l1_struct_0 @ sk_D)),
% 1.93/2.13      inference('sup-', [status(thm)], ['36', '37'])).
% 1.93/2.13  thf('57', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['55', '56'])).
% 1.93/2.13  thf('58', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['39', '57'])).
% 1.93/2.13  thf('59', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_E @ 
% 1.93/2.13        (k1_zfmisc_1 @ 
% 1.93/2.13         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.93/2.13      inference('demod', [status(thm)], ['32', '58'])).
% 1.93/2.13  thf('60', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.93/2.13  thf(t86_tmap_1, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.93/2.13             ( l1_pre_topc @ B ) ) =>
% 1.93/2.13           ( ![C:$i]:
% 1.93/2.13             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.13               ( ![D:$i]:
% 1.93/2.13                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.93/2.13                   ( ![E:$i]:
% 1.93/2.13                     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.13                         ( v1_funct_2 @
% 1.93/2.13                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.93/2.13                         ( m1_subset_1 @
% 1.93/2.13                           E @ 
% 1.93/2.13                           ( k1_zfmisc_1 @
% 1.93/2.13                             ( k2_zfmisc_1 @
% 1.93/2.13                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.93/2.13                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.93/2.13                         ( ![F:$i]:
% 1.93/2.13                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.93/2.13                             ( ![G:$i]:
% 1.93/2.13                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.93/2.13                                 ( ( ( F ) = ( G ) ) =>
% 1.93/2.13                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.93/2.13                                     ( r1_tmap_1 @
% 1.93/2.13                                       C @ B @ 
% 1.93/2.13                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.13  thf('61', plain,
% 1.93/2.13      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.93/2.13         ((v2_struct_0 @ X26)
% 1.93/2.13          | ~ (v2_pre_topc @ X26)
% 1.93/2.13          | ~ (l1_pre_topc @ X26)
% 1.93/2.13          | (v2_struct_0 @ X27)
% 1.93/2.13          | ~ (m1_pre_topc @ X27 @ X28)
% 1.93/2.13          | ~ (v1_tsep_1 @ X29 @ X27)
% 1.93/2.13          | ~ (m1_pre_topc @ X29 @ X27)
% 1.93/2.13          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 1.93/2.13          | ((X30) != (X31))
% 1.93/2.13          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 1.93/2.13               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 1.93/2.13          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X30)
% 1.93/2.13          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 1.93/2.13          | ~ (m1_subset_1 @ X32 @ 
% 1.93/2.13               (k1_zfmisc_1 @ 
% 1.93/2.13                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 1.93/2.13          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 1.93/2.13          | ~ (v1_funct_1 @ X32)
% 1.93/2.13          | ~ (m1_pre_topc @ X29 @ X28)
% 1.93/2.13          | (v2_struct_0 @ X29)
% 1.93/2.13          | ~ (l1_pre_topc @ X28)
% 1.93/2.13          | ~ (v2_pre_topc @ X28)
% 1.93/2.13          | (v2_struct_0 @ X28))),
% 1.93/2.13      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.93/2.13  thf('62', plain,
% 1.93/2.13      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 1.93/2.13         ((v2_struct_0 @ X28)
% 1.93/2.13          | ~ (v2_pre_topc @ X28)
% 1.93/2.13          | ~ (l1_pre_topc @ X28)
% 1.93/2.13          | (v2_struct_0 @ X29)
% 1.93/2.13          | ~ (m1_pre_topc @ X29 @ X28)
% 1.93/2.13          | ~ (v1_funct_1 @ X32)
% 1.93/2.13          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 1.93/2.13          | ~ (m1_subset_1 @ X32 @ 
% 1.93/2.13               (k1_zfmisc_1 @ 
% 1.93/2.13                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 1.93/2.13          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 1.93/2.13          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 1.93/2.13          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 1.93/2.13               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 1.93/2.13          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 1.93/2.13          | ~ (m1_pre_topc @ X29 @ X27)
% 1.93/2.13          | ~ (v1_tsep_1 @ X29 @ X27)
% 1.93/2.13          | ~ (m1_pre_topc @ X27 @ X28)
% 1.93/2.13          | (v2_struct_0 @ X27)
% 1.93/2.13          | ~ (l1_pre_topc @ X26)
% 1.93/2.13          | ~ (v2_pre_topc @ X26)
% 1.93/2.13          | (v2_struct_0 @ X26))),
% 1.93/2.13      inference('simplify', [status(thm)], ['61'])).
% 1.93/2.13  thf('63', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ X1 @ 
% 1.93/2.13             (k1_zfmisc_1 @ 
% 1.93/2.13              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.93/2.13          | (v2_struct_0 @ X0)
% 1.93/2.13          | ~ (v2_pre_topc @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | (v2_struct_0 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.93/2.13          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.93/2.13          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 1.93/2.13          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.93/2.13               X4)
% 1.93/2.13          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.93/2.13          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.93/2.13          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.93/2.13          | ~ (v1_funct_1 @ X1)
% 1.93/2.13          | ~ (m1_pre_topc @ X3 @ X2)
% 1.93/2.13          | (v2_struct_0 @ X3)
% 1.93/2.13          | ~ (l1_pre_topc @ X2)
% 1.93/2.13          | ~ (v2_pre_topc @ X2)
% 1.93/2.13          | (v2_struct_0 @ X2))),
% 1.93/2.13      inference('sup-', [status(thm)], ['60', '62'])).
% 1.93/2.13  thf('64', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.93/2.13  thf('65', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.93/2.13  thf('66', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ X1 @ 
% 1.93/2.13             (k1_zfmisc_1 @ 
% 1.93/2.13              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.93/2.13          | (v2_struct_0 @ X0)
% 1.93/2.13          | ~ (v2_pre_topc @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | (v2_struct_0 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.93/2.13          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.93/2.13          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 1.93/2.13          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.93/2.13               X4)
% 1.93/2.13          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.93/2.13          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.93/2.13          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.93/2.13          | ~ (v1_funct_1 @ X1)
% 1.93/2.13          | ~ (m1_pre_topc @ X3 @ X2)
% 1.93/2.13          | (v2_struct_0 @ X3)
% 1.93/2.13          | ~ (l1_pre_topc @ X2)
% 1.93/2.13          | ~ (v2_pre_topc @ X2)
% 1.93/2.13          | (v2_struct_0 @ X2))),
% 1.93/2.13      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.93/2.13  thf('67', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         ((v2_struct_0 @ X0)
% 1.93/2.13          | ~ (v2_pre_topc @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | (v2_struct_0 @ X1)
% 1.93/2.13          | ~ (m1_pre_topc @ X1 @ X0)
% 1.93/2.13          | ~ (v1_funct_1 @ sk_E)
% 1.93/2.13          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.93/2.13          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.93/2.13          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.93/2.13          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.93/2.13               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.93/2.13          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 1.93/2.13          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.93/2.13          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.93/2.13          | (v2_struct_0 @ sk_D)
% 1.93/2.13          | ~ (l1_pre_topc @ sk_B)
% 1.93/2.13          | ~ (v2_pre_topc @ sk_B)
% 1.93/2.13          | (v2_struct_0 @ sk_B))),
% 1.93/2.13      inference('sup-', [status(thm)], ['59', '66'])).
% 1.93/2.13  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('69', plain,
% 1.93/2.13      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('70', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 1.93/2.13  thf('71', plain,
% 1.93/2.13      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.93/2.13      inference('demod', [status(thm)], ['69', '70'])).
% 1.93/2.13  thf('72', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['39', '57'])).
% 1.93/2.13  thf('73', plain,
% 1.93/2.13      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.93/2.13      inference('demod', [status(thm)], ['71', '72'])).
% 1.93/2.13  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('75', plain, ((v2_pre_topc @ sk_B)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('76', plain,
% 1.93/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.13         ((v2_struct_0 @ X0)
% 1.93/2.13          | ~ (v2_pre_topc @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | (v2_struct_0 @ X1)
% 1.93/2.13          | ~ (m1_pre_topc @ X1 @ X0)
% 1.93/2.13          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.93/2.13          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.93/2.13          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.93/2.13               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.93/2.13          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 1.93/2.13          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.93/2.13          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.93/2.13          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.93/2.13          | (v2_struct_0 @ sk_D)
% 1.93/2.13          | (v2_struct_0 @ sk_B))),
% 1.93/2.13      inference('demod', [status(thm)], ['67', '68', '73', '74', '75'])).
% 1.93/2.13  thf('77', plain,
% 1.93/2.13      (((v2_struct_0 @ sk_B)
% 1.93/2.13        | (v2_struct_0 @ sk_D)
% 1.93/2.13        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.93/2.13        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.93/2.13        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.93/2.13        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.93/2.13        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.93/2.13        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.93/2.13        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.13        | (v2_struct_0 @ sk_C)
% 1.93/2.13        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.13        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.13        | (v2_struct_0 @ sk_A))),
% 1.93/2.13      inference('sup-', [status(thm)], ['3', '76'])).
% 1.93/2.13  thf('78', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('79', plain,
% 1.93/2.13      (![X3 : $i]:
% 1.93/2.13         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.93/2.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.93/2.13  thf(t2_tsep_1, axiom,
% 1.93/2.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.93/2.13  thf('80', plain,
% 1.93/2.13      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.93/2.13      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.13  thf(t1_tsep_1, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_pre_topc @ A ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( m1_pre_topc @ B @ A ) =>
% 1.93/2.13           ( m1_subset_1 @
% 1.93/2.13             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.93/2.13  thf('81', plain,
% 1.93/2.13      (![X20 : $i, X21 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X20 @ X21)
% 1.93/2.13          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.93/2.13          | ~ (l1_pre_topc @ X21))),
% 1.93/2.13      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.93/2.13  thf('82', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (l1_pre_topc @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0)
% 1.93/2.13          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.93/2.13      inference('sup-', [status(thm)], ['80', '81'])).
% 1.93/2.13  thf('83', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('simplify', [status(thm)], ['82'])).
% 1.93/2.13  thf('84', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.93/2.13          | ~ (l1_struct_0 @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('sup+', [status(thm)], ['79', '83'])).
% 1.93/2.13  thf('85', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.93/2.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.93/2.13  thf('86', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (l1_pre_topc @ X0)
% 1.93/2.13          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.93/2.13      inference('clc', [status(thm)], ['84', '85'])).
% 1.93/2.13  thf('87', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 1.93/2.13  thf(t16_tsep_1, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( m1_pre_topc @ B @ A ) =>
% 1.93/2.13           ( ![C:$i]:
% 1.93/2.13             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.93/2.13               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.93/2.13                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.93/2.13                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.93/2.13  thf('88', plain,
% 1.93/2.13      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X17 @ X18)
% 1.93/2.13          | ((X19) != (u1_struct_0 @ X17))
% 1.93/2.13          | ~ (v3_pre_topc @ X19 @ X18)
% 1.93/2.13          | (v1_tsep_1 @ X17 @ X18)
% 1.93/2.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.93/2.13          | ~ (l1_pre_topc @ X18)
% 1.93/2.13          | ~ (v2_pre_topc @ X18))),
% 1.93/2.13      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.93/2.13  thf('89', plain,
% 1.93/2.13      (![X17 : $i, X18 : $i]:
% 1.93/2.13         (~ (v2_pre_topc @ X18)
% 1.93/2.13          | ~ (l1_pre_topc @ X18)
% 1.93/2.13          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 1.93/2.13               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.93/2.13          | (v1_tsep_1 @ X17 @ X18)
% 1.93/2.13          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 1.93/2.13          | ~ (m1_pre_topc @ X17 @ X18))),
% 1.93/2.13      inference('simplify', [status(thm)], ['88'])).
% 1.93/2.13  thf('90', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 1.93/2.13          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.93/2.13          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.93/2.13          | (v1_tsep_1 @ X0 @ sk_D)
% 1.93/2.13          | ~ (l1_pre_topc @ sk_D)
% 1.93/2.13          | ~ (v2_pre_topc @ sk_D))),
% 1.93/2.13      inference('sup-', [status(thm)], ['87', '89'])).
% 1.93/2.13  thf('91', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('92', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(cc1_pre_topc, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.93/2.13  thf('93', plain,
% 1.93/2.13      (![X1 : $i, X2 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X1 @ X2)
% 1.93/2.13          | (v2_pre_topc @ X1)
% 1.93/2.13          | ~ (l1_pre_topc @ X2)
% 1.93/2.13          | ~ (v2_pre_topc @ X2))),
% 1.93/2.13      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.93/2.13  thf('94', plain,
% 1.93/2.13      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.93/2.13      inference('sup-', [status(thm)], ['92', '93'])).
% 1.93/2.13  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('97', plain, ((v2_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.93/2.13  thf('98', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 1.93/2.13          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.93/2.13          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.93/2.13          | (v1_tsep_1 @ X0 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['90', '91', '97'])).
% 1.93/2.13  thf('99', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['39', '57'])).
% 1.93/2.13  thf('100', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.93/2.13             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.93/2.13          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.93/2.13          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.93/2.13          | (v1_tsep_1 @ X0 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['98', '99'])).
% 1.93/2.13  thf('101', plain,
% 1.93/2.13      ((~ (l1_pre_topc @ sk_C)
% 1.93/2.13        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.93/2.13        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.93/2.13        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 1.93/2.13      inference('sup-', [status(thm)], ['86', '100'])).
% 1.93/2.13  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['18', '19'])).
% 1.93/2.13  thf('103', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['39', '57'])).
% 1.93/2.13  thf('104', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['55', '56'])).
% 1.93/2.13  thf(fc10_tops_1, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.13       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.93/2.13  thf('105', plain,
% 1.93/2.13      (![X13 : $i]:
% 1.93/2.13         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 1.93/2.13          | ~ (l1_pre_topc @ X13)
% 1.93/2.13          | ~ (v2_pre_topc @ X13))),
% 1.93/2.13      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.93/2.13  thf('106', plain,
% 1.93/2.13      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 1.93/2.13        | ~ (v2_pre_topc @ sk_D)
% 1.93/2.13        | ~ (l1_pre_topc @ sk_D))),
% 1.93/2.13      inference('sup+', [status(thm)], ['104', '105'])).
% 1.93/2.13  thf('107', plain, ((v2_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.93/2.13  thf('108', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('109', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.93/2.13  thf('110', plain,
% 1.93/2.13      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.93/2.13      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.93/2.13  thf('111', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf(t12_tmap_1, axiom,
% 1.93/2.13    (![A:$i]:
% 1.93/2.13     ( ( l1_pre_topc @ A ) =>
% 1.93/2.13       ( ![B:$i]:
% 1.93/2.13         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 1.93/2.13           ( ![C:$i]:
% 1.93/2.13             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 1.93/2.13               ( ( ( B ) =
% 1.93/2.13                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 1.93/2.13                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.93/2.13  thf('112', plain,
% 1.93/2.13      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.13         (~ (v2_pre_topc @ X14)
% 1.93/2.13          | ~ (l1_pre_topc @ X14)
% 1.93/2.13          | ((X14) != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 1.93/2.13          | ~ (m1_pre_topc @ X14 @ X16)
% 1.93/2.13          | (m1_pre_topc @ X15 @ X16)
% 1.93/2.13          | ~ (l1_pre_topc @ X15)
% 1.93/2.13          | ~ (v2_pre_topc @ X15)
% 1.93/2.13          | ~ (l1_pre_topc @ X16))),
% 1.93/2.13      inference('cnf', [status(esa)], [t12_tmap_1])).
% 1.93/2.13  thf('113', plain,
% 1.93/2.13      (![X15 : $i, X16 : $i]:
% 1.93/2.13         (~ (l1_pre_topc @ X16)
% 1.93/2.13          | ~ (v2_pre_topc @ X15)
% 1.93/2.13          | ~ (l1_pre_topc @ X15)
% 1.93/2.13          | (m1_pre_topc @ X15 @ X16)
% 1.93/2.13          | ~ (m1_pre_topc @ 
% 1.93/2.13               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)) @ X16)
% 1.93/2.13          | ~ (l1_pre_topc @ 
% 1.93/2.13               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 1.93/2.13          | ~ (v2_pre_topc @ 
% 1.93/2.13               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))),
% 1.93/2.13      inference('simplify', [status(thm)], ['112'])).
% 1.93/2.13  thf('114', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (l1_pre_topc @ sk_D)
% 1.93/2.13          | ~ (v2_pre_topc @ 
% 1.93/2.13               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.93/2.13          | ~ (m1_pre_topc @ 
% 1.93/2.13               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 1.93/2.13          | (m1_pre_topc @ sk_C @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ sk_C)
% 1.93/2.13          | ~ (v2_pre_topc @ sk_C)
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['111', '113'])).
% 1.93/2.13  thf('115', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('116', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('117', plain, ((v2_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.93/2.13  thf('118', plain,
% 1.93/2.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('119', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['18', '19'])).
% 1.93/2.13  thf('120', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('121', plain,
% 1.93/2.13      (![X1 : $i, X2 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ X1 @ X2)
% 1.93/2.13          | (v2_pre_topc @ X1)
% 1.93/2.13          | ~ (l1_pre_topc @ X2)
% 1.93/2.13          | ~ (v2_pre_topc @ X2))),
% 1.93/2.13      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.93/2.13  thf('122', plain,
% 1.93/2.13      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.93/2.13      inference('sup-', [status(thm)], ['120', '121'])).
% 1.93/2.13  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('125', plain, ((v2_pre_topc @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.93/2.13  thf('126', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (~ (m1_pre_topc @ sk_D @ X0)
% 1.93/2.13          | (m1_pre_topc @ sk_C @ X0)
% 1.93/2.13          | ~ (l1_pre_topc @ X0))),
% 1.93/2.13      inference('demod', [status(thm)],
% 1.93/2.13                ['114', '115', '116', '117', '118', '119', '125'])).
% 1.93/2.13  thf('127', plain,
% 1.93/2.13      ((~ (l1_pre_topc @ sk_D)
% 1.93/2.13        | ~ (l1_pre_topc @ sk_D)
% 1.93/2.13        | (m1_pre_topc @ sk_C @ sk_D))),
% 1.93/2.13      inference('sup-', [status(thm)], ['110', '126'])).
% 1.93/2.13  thf('128', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('129', plain, ((l1_pre_topc @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.13  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['127', '128', '129'])).
% 1.93/2.13  thf('131', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['101', '102', '103', '109', '130'])).
% 1.93/2.13  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['127', '128', '129'])).
% 1.93/2.13  thf('133', plain,
% 1.93/2.13      (![X3 : $i]:
% 1.93/2.13         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.93/2.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.93/2.13  thf('134', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('135', plain, (((sk_F) = (sk_G))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('136', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['134', '135'])).
% 1.93/2.13  thf('137', plain,
% 1.93/2.13      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 1.93/2.13      inference('sup+', [status(thm)], ['133', '136'])).
% 1.93/2.13  thf('138', plain, ((l1_struct_0 @ sk_C)),
% 1.93/2.13      inference('sup-', [status(thm)], ['44', '45'])).
% 1.93/2.13  thf('139', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['137', '138'])).
% 1.93/2.13  thf('140', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['39', '57'])).
% 1.93/2.13  thf('141', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['137', '138'])).
% 1.93/2.13  thf('142', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('145', plain,
% 1.93/2.13      (((v2_struct_0 @ sk_B)
% 1.93/2.13        | (v2_struct_0 @ sk_D)
% 1.93/2.13        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.93/2.13        | (v2_struct_0 @ sk_C)
% 1.93/2.13        | (v2_struct_0 @ sk_A))),
% 1.93/2.13      inference('demod', [status(thm)],
% 1.93/2.13                ['77', '78', '131', '132', '139', '140', '141', '142', '143', 
% 1.93/2.13                 '144'])).
% 1.93/2.13  thf('146', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('147', plain,
% 1.93/2.13      (((v2_struct_0 @ sk_A)
% 1.93/2.13        | (v2_struct_0 @ sk_C)
% 1.93/2.13        | (v2_struct_0 @ sk_D)
% 1.93/2.13        | (v2_struct_0 @ sk_B))),
% 1.93/2.13      inference('sup-', [status(thm)], ['145', '146'])).
% 1.93/2.13  thf('148', plain, (~ (v2_struct_0 @ sk_D)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('149', plain,
% 1.93/2.13      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.93/2.13      inference('sup-', [status(thm)], ['147', '148'])).
% 1.93/2.13  thf('150', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('151', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.93/2.13      inference('clc', [status(thm)], ['149', '150'])).
% 1.93/2.13  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('153', plain, ((v2_struct_0 @ sk_C)),
% 1.93/2.13      inference('clc', [status(thm)], ['151', '152'])).
% 1.93/2.13  thf('154', plain, ($false), inference('demod', [status(thm)], ['0', '153'])).
% 1.93/2.13  
% 1.93/2.13  % SZS output end Refutation
% 1.93/2.13  
% 1.93/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
