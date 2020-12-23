%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9haH57k2Oo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:30 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 990 expanded)
%              Number of leaves         :   38 ( 303 expanded)
%              Depth                    :   20
%              Number of atoms          : 1510 (30547 expanded)
%              Number of equality atoms :   35 ( 965 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_pre_topc @ X12 @ X13 )
       != ( g1_pre_topc @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('14',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_connsp_2 @ ( sk_C @ X20 @ X19 ) @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('35',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_C @ X0 @ sk_D ) @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference('sup-',[status(thm)],['3','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_D @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('49',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_D @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf(t83_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X32 )
      | ( X32 != X30 )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X32 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','22','23','28','29'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('81',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['80','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('87',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('90',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','87','88','89','90','91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','93'])).

thf('95',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference('sup-',[status(thm)],['3','42'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','97','98'])).

thf('100',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9haH57k2Oo
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 251 iterations in 0.159s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.61  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.61  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.38/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.61  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(t88_tmap_1, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61             ( l1_pre_topc @ B ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61               ( ![D:$i]:
% 0.38/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                   ( ![E:$i]:
% 0.38/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                         ( v1_funct_2 @
% 0.38/0.61                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                         ( m1_subset_1 @
% 0.38/0.61                           E @ 
% 0.38/0.61                           ( k1_zfmisc_1 @
% 0.38/0.61                             ( k2_zfmisc_1 @
% 0.38/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                       ( ( ( g1_pre_topc @
% 0.38/0.61                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.61                           ( D ) ) =>
% 0.38/0.61                         ( ![F:$i]:
% 0.38/0.61                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.61                             ( ![G:$i]:
% 0.38/0.61                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.61                                 ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.61                                     ( r1_tmap_1 @
% 0.38/0.61                                       C @ B @ 
% 0.38/0.61                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.61                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61                ( l1_pre_topc @ B ) ) =>
% 0.38/0.61              ( ![C:$i]:
% 0.38/0.61                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61                  ( ![D:$i]:
% 0.38/0.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                      ( ![E:$i]:
% 0.38/0.61                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                            ( v1_funct_2 @
% 0.38/0.61                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                            ( m1_subset_1 @
% 0.38/0.61                              E @ 
% 0.38/0.61                              ( k1_zfmisc_1 @
% 0.38/0.61                                ( k2_zfmisc_1 @
% 0.38/0.61                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                          ( ( ( g1_pre_topc @
% 0.38/0.61                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.61                              ( D ) ) =>
% 0.38/0.61                            ( ![F:$i]:
% 0.38/0.61                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.61                                ( ![G:$i]:
% 0.38/0.61                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.61                                    ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.61                                        ( r1_tmap_1 @
% 0.38/0.61                                          C @ B @ 
% 0.38/0.61                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.61                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.38/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('2', plain, (((sk_F) = (sk_G))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.38/0.61         = (sk_D))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(abstractness_v1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ( v1_pre_topc @ A ) =>
% 0.38/0.61         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X3 : $i]:
% 0.38/0.61         (~ (v1_pre_topc @ X3)
% 0.38/0.61          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.38/0.61          | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.38/0.61  thf(dt_u1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( m1_subset_1 @
% 0.38/0.61         ( u1_pre_topc @ A ) @ 
% 0.38/0.61         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X8 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.38/0.61          | ~ (l1_pre_topc @ X8))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.38/0.61  thf(free_g1_pre_topc, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.61       ( ![C:$i,D:$i]:
% 0.38/0.61         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.38/0.61           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.61         (((g1_pre_topc @ X12 @ X13) != (g1_pre_topc @ X10 @ X11))
% 0.38/0.61          | ((X12) = (X10))
% 0.38/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.38/0.61      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X0)
% 0.38/0.61          | ((u1_struct_0 @ X0) = (X1))
% 0.38/0.61          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.38/0.61              != (g1_pre_topc @ X1 @ X2)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v1_pre_topc @ X0)
% 0.38/0.61          | ((u1_struct_0 @ X0) = (X2))
% 0.38/0.61          | ~ (l1_pre_topc @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X1 : $i, X2 : $i]:
% 0.38/0.61         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.38/0.61          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.38/0.61          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      ((~ (v1_pre_topc @ sk_D)
% 0.38/0.61        | ~ (l1_pre_topc @ 
% 0.38/0.61             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.38/0.61        | ((u1_struct_0 @ 
% 0.38/0.61            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.38/0.61            = (u1_struct_0 @ sk_C_1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.38/0.61         = (sk_D))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(fc7_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ( ~( v2_struct_0 @
% 0.38/0.61              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.38/0.61         ( v1_pre_topc @
% 0.38/0.61           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X9 : $i]:
% 0.38/0.61         ((v1_pre_topc @ 
% 0.38/0.61           (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.38/0.61          | ~ (l1_pre_topc @ X9)
% 0.38/0.61          | (v2_struct_0 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (((v1_pre_topc @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_C_1)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_C_1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('15', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(dt_m1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.61  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('19', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('20', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['14', '19'])).
% 0.38/0.61  thf('21', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('22', plain, ((v1_pre_topc @ sk_D)),
% 0.38/0.61      inference('clc', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.38/0.61         = (sk_D))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.61  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.38/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('28', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.38/0.61         = (sk_D))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('30', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf(existence_m1_connsp_2, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X19)
% 0.38/0.61          | ~ (v2_pre_topc @ X19)
% 0.38/0.61          | (v2_struct_0 @ X19)
% 0.38/0.61          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.38/0.61          | (m1_connsp_2 @ (sk_C @ X20 @ X19) @ X19 @ X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | (m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_D))),
% 0.38/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.61  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(cc1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]:
% 0.38/0.61         (~ (m1_pre_topc @ X4 @ X5)
% 0.38/0.61          | (v2_pre_topc @ X4)
% 0.38/0.61          | ~ (l1_pre_topc @ X5)
% 0.38/0.61          | ~ (v2_pre_topc @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.38/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('38', plain, ((v2_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.61  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | (m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D))),
% 0.38/0.61      inference('demod', [status(thm)], ['32', '38', '39'])).
% 0.38/0.61  thf('41', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_connsp_2 @ (sk_C @ X0 @ sk_D) @ sk_D @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.61      inference('clc', [status(thm)], ['40', '41'])).
% 0.38/0.61  thf('43', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '42'])).
% 0.38/0.61  thf('44', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('45', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf(dt_m1_connsp_2, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61       ( ![C:$i]:
% 0.38/0.61         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.38/0.61           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X16)
% 0.38/0.61          | ~ (v2_pre_topc @ X16)
% 0.38/0.61          | (v2_struct_0 @ X16)
% 0.38/0.61          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.61          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.61          | ~ (m1_connsp_2 @ X18 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (m1_connsp_2 @ X1 @ sk_D @ X0)
% 0.38/0.61          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_D))),
% 0.38/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.61  thf('48', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('49', plain, ((v2_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.61  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (m1_connsp_2 @ X1 @ sk_D @ X0)
% 0.38/0.61          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | (v2_struct_0 @ sk_D))),
% 0.38/0.61      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_D)
% 0.38/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.38/0.61      inference('sup-', [status(thm)], ['44', '51'])).
% 0.38/0.61  thf('53', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.38/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.38/0.61      inference('clc', [status(thm)], ['52', '53'])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.38/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['43', '54'])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.61        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('57', plain, (((sk_F) = (sk_G))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.38/0.61        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.38/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('60', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_E @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.61  thf('62', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf(t83_tmap_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.61             ( l1_pre_topc @ B ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.61               ( ![D:$i]:
% 0.38/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.61                   ( ![E:$i]:
% 0.38/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.61                         ( v1_funct_2 @
% 0.38/0.61                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.61                         ( m1_subset_1 @
% 0.38/0.61                           E @ 
% 0.38/0.61                           ( k1_zfmisc_1 @
% 0.38/0.61                             ( k2_zfmisc_1 @
% 0.38/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.61                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.61                         ( ![F:$i]:
% 0.38/0.61                           ( ( m1_subset_1 @
% 0.38/0.61                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.38/0.61                             ( ![G:$i]:
% 0.38/0.61                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.61                                 ( ![H:$i]:
% 0.38/0.61                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.61                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.61                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.38/0.61                                         ( ( G ) = ( H ) ) ) =>
% 0.38/0.61                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.38/0.61                                         ( r1_tmap_1 @
% 0.38/0.61                                           C @ B @ 
% 0.38/0.61                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.38/0.61                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('63', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 0.38/0.61         X32 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X25)
% 0.38/0.61          | ~ (v2_pre_topc @ X25)
% 0.38/0.61          | ~ (l1_pre_topc @ X25)
% 0.38/0.61          | (v2_struct_0 @ X26)
% 0.38/0.61          | ~ (m1_pre_topc @ X26 @ X27)
% 0.38/0.61          | ~ (m1_pre_topc @ X28 @ X26)
% 0.38/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.38/0.61          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.38/0.61               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.38/0.61          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X32)
% 0.38/0.61          | ((X32) != (X30))
% 0.38/0.61          | ~ (m1_connsp_2 @ X29 @ X26 @ X32)
% 0.38/0.61          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.38/0.61          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X26))
% 0.38/0.61          | ~ (m1_subset_1 @ X31 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.38/0.61          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.38/0.61          | ~ (v1_funct_1 @ X31)
% 0.38/0.61          | ~ (m1_pre_topc @ X28 @ X27)
% 0.38/0.61          | (v2_struct_0 @ X28)
% 0.38/0.61          | ~ (l1_pre_topc @ X27)
% 0.38/0.61          | ~ (v2_pre_topc @ X27)
% 0.38/0.61          | (v2_struct_0 @ X27))),
% 0.38/0.61      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X27)
% 0.38/0.61          | ~ (v2_pre_topc @ X27)
% 0.38/0.61          | ~ (l1_pre_topc @ X27)
% 0.38/0.61          | (v2_struct_0 @ X28)
% 0.38/0.61          | ~ (m1_pre_topc @ X28 @ X27)
% 0.38/0.61          | ~ (v1_funct_1 @ X31)
% 0.38/0.61          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.38/0.61          | ~ (m1_subset_1 @ X31 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.38/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.38/0.61          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.38/0.61          | ~ (m1_connsp_2 @ X29 @ X26 @ X30)
% 0.38/0.61          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.38/0.61          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.38/0.61               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.38/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.38/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.61          | ~ (m1_pre_topc @ X28 @ X26)
% 0.38/0.61          | ~ (m1_pre_topc @ X26 @ X27)
% 0.38/0.61          | (v2_struct_0 @ X26)
% 0.38/0.61          | ~ (l1_pre_topc @ X25)
% 0.38/0.61          | ~ (v2_pre_topc @ X25)
% 0.38/0.61          | (v2_struct_0 @ X25))),
% 0.38/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.38/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.61          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.61          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.38/0.61               X5)
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.38/0.61          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.38/0.61          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.38/0.61          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X2)
% 0.38/0.61          | (v2_struct_0 @ X3)
% 0.38/0.61          | ~ (l1_pre_topc @ X2)
% 0.38/0.61          | ~ (v2_pre_topc @ X2)
% 0.38/0.61          | (v2_struct_0 @ X2))),
% 0.38/0.61      inference('sup-', [status(thm)], ['62', '64'])).
% 0.38/0.61  thf('66', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('67', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('68', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.38/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.61          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.38/0.61               X5)
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.38/0.61          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.38/0.61          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.38/0.61          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X3 @ X2)
% 0.38/0.61          | (v2_struct_0 @ X3)
% 0.38/0.61          | ~ (l1_pre_topc @ X2)
% 0.38/0.61          | ~ (v2_pre_topc @ X2)
% 0.38/0.61          | (v2_struct_0 @ X2))),
% 0.38/0.61      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.61               (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.61          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.38/0.61          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.61               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['61', '69'])).
% 0.38/0.61  thf('71', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('73', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '22', '23', '28', '29'])).
% 0.38/0.61  thf('74', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.38/0.61  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('77', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v2_struct_0 @ X1)
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.61          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.38/0.61          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.61               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.38/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['70', '71', '74', '75', '76'])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.61          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.61          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.38/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_C_1)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['58', '77'])).
% 0.38/0.61  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('80', plain,
% 0.38/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.38/0.61         = (sk_D))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t2_tsep_1, axiom,
% 0.38/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.38/0.61  thf('81', plain,
% 0.38/0.61      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.61  thf(t65_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( l1_pre_topc @ B ) =>
% 0.38/0.61           ( ( m1_pre_topc @ A @ B ) <=>
% 0.38/0.61             ( m1_pre_topc @
% 0.38/0.61               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.38/0.61  thf('82', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X14)
% 0.38/0.61          | ~ (m1_pre_topc @ X15 @ X14)
% 0.38/0.61          | (m1_pre_topc @ X15 @ 
% 0.38/0.61             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.38/0.61          | ~ (l1_pre_topc @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.38/0.61  thf('83', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (m1_pre_topc @ X0 @ 
% 0.38/0.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.61          | ~ (l1_pre_topc @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['81', '82'])).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((m1_pre_topc @ X0 @ 
% 0.38/0.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.61          | ~ (l1_pre_topc @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['83'])).
% 0.38/0.61  thf('85', plain,
% 0.38/0.61      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['80', '84'])).
% 0.38/0.61  thf('86', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('87', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.38/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.61  thf('88', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('89', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('90', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('93', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_D)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.61          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.38/0.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61          | (v2_struct_0 @ sk_C_1)
% 0.38/0.61          | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['78', '79', '87', '88', '89', '90', '91', '92'])).
% 0.38/0.61  thf('94', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_C_1)
% 0.38/0.61        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.61        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.38/0.61        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['55', '93'])).
% 0.38/0.61  thf('95', plain,
% 0.38/0.61      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.38/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['43', '54'])).
% 0.38/0.61  thf(t3_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('96', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('97', plain,
% 0.38/0.61      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.61  thf('98', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '42'])).
% 0.38/0.61  thf('99', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_C_1)
% 0.38/0.61        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['94', '97', '98'])).
% 0.38/0.61  thf('100', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('101', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_D)
% 0.38/0.61        | (v2_struct_0 @ sk_C_1)
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.61  thf('102', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('103', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.38/0.61  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('105', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.38/0.61      inference('clc', [status(thm)], ['103', '104'])).
% 0.38/0.61  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('107', plain, ((v2_struct_0 @ sk_C_1)),
% 0.38/0.61      inference('clc', [status(thm)], ['105', '106'])).
% 0.38/0.61  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
