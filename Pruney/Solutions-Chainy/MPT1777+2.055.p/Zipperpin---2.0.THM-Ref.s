%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ox70tJqUwj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  159 (1711 expanded)
%              Number of leaves         :   35 ( 510 expanded)
%              Depth                    :   22
%              Number of atoms          : 1551 (48320 expanded)
%              Number of equality atoms :   22 (1214 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_connsp_2 @ ( sk_C @ X16 @ X15 ) @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('3',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['3','9','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_connsp_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('22',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('28',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['32','33','34','39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('48',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('55',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','46','47','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('63',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['32','33','34','39'])).

thf('70',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62','68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','71'])).

thf('73',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

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

thf('80',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X31 )
      | ( X31 != X29 )
      | ~ ( m1_connsp_2 @ X28 @ X25 @ X31 )
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('81',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X28 @ X25 @ X29 )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X29 )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('86',plain,(
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
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('91',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
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
    inference(demod,[status(thm)],['87','88','91','92','93'])).

thf('95',plain,(
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
    inference('sup-',[status(thm)],['75','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('98',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('102',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','100','101','102','103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','105'])).

thf('107',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','70'])).

thf('111',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','111','112'])).

thf('114',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ox70tJqUwj
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.57  % Solved by: fo/fo7.sh
% 0.19/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.57  % done 188 iterations in 0.126s
% 0.19/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.57  % SZS output start Refutation
% 0.19/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.19/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.19/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.57  thf(t88_tmap_1, conjecture,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.57             ( l1_pre_topc @ B ) ) =>
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.57               ( ![D:$i]:
% 0.19/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.57                   ( ![E:$i]:
% 0.19/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.57                         ( v1_funct_2 @
% 0.19/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.57                         ( m1_subset_1 @
% 0.19/0.57                           E @ 
% 0.19/0.57                           ( k1_zfmisc_1 @
% 0.19/0.57                             ( k2_zfmisc_1 @
% 0.19/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.57                       ( ( ( g1_pre_topc @
% 0.19/0.57                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.19/0.57                           ( D ) ) =>
% 0.19/0.57                         ( ![F:$i]:
% 0.19/0.57                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.57                             ( ![G:$i]:
% 0.19/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.57                                 ( ( ( ( F ) = ( G ) ) & 
% 0.19/0.57                                     ( r1_tmap_1 @
% 0.19/0.57                                       C @ B @ 
% 0.19/0.57                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.19/0.57                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.57    (~( ![A:$i]:
% 0.19/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.57            ( l1_pre_topc @ A ) ) =>
% 0.19/0.57          ( ![B:$i]:
% 0.19/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.57                ( l1_pre_topc @ B ) ) =>
% 0.19/0.57              ( ![C:$i]:
% 0.19/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.57                  ( ![D:$i]:
% 0.19/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.57                      ( ![E:$i]:
% 0.19/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.57                            ( v1_funct_2 @
% 0.19/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.57                            ( m1_subset_1 @
% 0.19/0.57                              E @ 
% 0.19/0.57                              ( k1_zfmisc_1 @
% 0.19/0.57                                ( k2_zfmisc_1 @
% 0.19/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.57                          ( ( ( g1_pre_topc @
% 0.19/0.57                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.19/0.57                              ( D ) ) =>
% 0.19/0.57                            ( ![F:$i]:
% 0.19/0.57                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.57                                ( ![G:$i]:
% 0.19/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.57                                    ( ( ( ( F ) = ( G ) ) & 
% 0.19/0.57                                        ( r1_tmap_1 @
% 0.19/0.57                                          C @ B @ 
% 0.19/0.57                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.19/0.57                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.57    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.19/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(existence_m1_connsp_2, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.57       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.19/0.57  thf('2', plain,
% 0.19/0.57      (![X15 : $i, X16 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X15)
% 0.19/0.57          | ~ (v2_pre_topc @ X15)
% 0.19/0.57          | (v2_struct_0 @ X15)
% 0.19/0.57          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.19/0.57          | (m1_connsp_2 @ (sk_C @ X16 @ X15) @ X15 @ X16))),
% 0.19/0.57      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.19/0.57  thf('3', plain,
% 0.19/0.57      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.19/0.57        | (v2_struct_0 @ sk_D)
% 0.19/0.57        | ~ (v2_pre_topc @ sk_D)
% 0.19/0.57        | ~ (l1_pre_topc @ sk_D))),
% 0.19/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.57  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(cc1_pre_topc, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.57  thf('5', plain,
% 0.19/0.57      (![X6 : $i, X7 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X6 @ X7)
% 0.19/0.57          | (v2_pre_topc @ X6)
% 0.19/0.57          | ~ (l1_pre_topc @ X7)
% 0.19/0.57          | ~ (v2_pre_topc @ X7))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.57  thf('6', plain,
% 0.19/0.57      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.19/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.57  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.57  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_m1_pre_topc, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l1_pre_topc @ A ) =>
% 0.19/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.57  thf('11', plain,
% 0.19/0.57      (![X8 : $i, X9 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.57  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.57  thf('15', plain,
% 0.19/0.57      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.19/0.57        | (v2_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['3', '9', '14'])).
% 0.19/0.57  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.19/0.57      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.57  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_m1_connsp_2, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.57       ( ![C:$i]:
% 0.19/0.57         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.19/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.57  thf('19', plain,
% 0.19/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X12)
% 0.19/0.57          | ~ (v2_pre_topc @ X12)
% 0.19/0.57          | (v2_struct_0 @ X12)
% 0.19/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.19/0.57          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.57          | ~ (m1_connsp_2 @ X14 @ X12 @ X13))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.19/0.57  thf('20', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.19/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.57          | ~ (l1_pre_topc @ sk_D))),
% 0.19/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.57  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.57  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.57  thf('23', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.19/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.57          | (v2_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.57  thf('24', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('25', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.19/0.57      inference('clc', [status(thm)], ['23', '24'])).
% 0.19/0.57  thf('26', plain,
% 0.19/0.57      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.19/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['17', '25'])).
% 0.19/0.57  thf('27', plain,
% 0.19/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.19/0.57         = (sk_D))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(t2_tsep_1, axiom,
% 0.19/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.19/0.57  thf('28', plain,
% 0.19/0.57      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.19/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.19/0.57  thf(t65_pre_topc, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l1_pre_topc @ A ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( l1_pre_topc @ B ) =>
% 0.19/0.57           ( ( m1_pre_topc @ A @ B ) <=>
% 0.19/0.57             ( m1_pre_topc @
% 0.19/0.57               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.19/0.57  thf('29', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X10)
% 0.19/0.57          | ~ (m1_pre_topc @ X11 @ 
% 0.19/0.57               (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.19/0.57          | (m1_pre_topc @ X11 @ X10)
% 0.19/0.57          | ~ (l1_pre_topc @ X11))),
% 0.19/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.19/0.57  thf('30', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ 
% 0.19/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.57          | ~ (l1_pre_topc @ 
% 0.19/0.57               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.57          | (m1_pre_topc @ 
% 0.19/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0))),
% 0.19/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.57  thf('31', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X0)
% 0.19/0.57          | (m1_pre_topc @ 
% 0.19/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ 
% 0.19/0.57               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.19/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.57  thf('32', plain,
% 0.19/0.57      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.57        | (m1_pre_topc @ 
% 0.19/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 0.19/0.57           sk_C_1)
% 0.19/0.57        | ~ (l1_pre_topc @ sk_C_1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['27', '31'])).
% 0.19/0.57  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.57  thf('34', plain,
% 0.19/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.19/0.57         = (sk_D))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('36', plain,
% 0.19/0.57      (![X8 : $i, X9 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.57  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.57  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('39', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.57  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['32', '33', '34', '39'])).
% 0.19/0.57  thf('41', plain,
% 0.19/0.57      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.19/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.19/0.57  thf(t4_tsep_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.57               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.19/0.57                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.57  thf('42', plain,
% 0.19/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X18 @ X19)
% 0.19/0.57          | ~ (m1_pre_topc @ X18 @ X20)
% 0.19/0.57          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 0.19/0.57          | ~ (m1_pre_topc @ X20 @ X19)
% 0.19/0.57          | ~ (l1_pre_topc @ X19)
% 0.19/0.57          | ~ (v2_pre_topc @ X19))),
% 0.19/0.57      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.19/0.57  thf('43', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.57  thf('44', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0))),
% 0.19/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.57  thf('45', plain,
% 0.19/0.57      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.57        | ~ (v2_pre_topc @ sk_D)
% 0.19/0.57        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.19/0.57        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['40', '44'])).
% 0.19/0.57  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.57  thf('47', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.57  thf('48', plain,
% 0.19/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.19/0.57         = (sk_D))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('49', plain,
% 0.19/0.57      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.19/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X10)
% 0.19/0.57          | ~ (m1_pre_topc @ X11 @ X10)
% 0.19/0.57          | (m1_pre_topc @ X11 @ 
% 0.19/0.57             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.19/0.57          | ~ (l1_pre_topc @ X11))),
% 0.19/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.19/0.57  thf('51', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (l1_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | (m1_pre_topc @ X0 @ 
% 0.19/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.57          | ~ (l1_pre_topc @ X0))),
% 0.19/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.57  thf('52', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((m1_pre_topc @ X0 @ 
% 0.19/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.19/0.57          | ~ (l1_pre_topc @ X0))),
% 0.19/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.19/0.57  thf('53', plain,
% 0.19/0.57      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 0.19/0.57      inference('sup+', [status(thm)], ['48', '52'])).
% 0.19/0.57  thf('54', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.57  thf('55', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.57  thf('56', plain,
% 0.19/0.57      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('demod', [status(thm)], ['45', '46', '47', '55'])).
% 0.19/0.57  thf(d10_xboole_0, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.57  thf('57', plain,
% 0.19/0.57      (![X0 : $i, X2 : $i]:
% 0.19/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.57  thf('58', plain,
% 0.19/0.57      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.19/0.57        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.57  thf('59', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.57  thf('60', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0))),
% 0.19/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.57  thf('61', plain,
% 0.19/0.57      ((~ (l1_pre_topc @ sk_C_1)
% 0.19/0.57        | ~ (v2_pre_topc @ sk_C_1)
% 0.19/0.57        | ~ (m1_pre_topc @ sk_D @ sk_C_1)
% 0.19/0.57        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.57  thf('62', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.57  thf('63', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('64', plain,
% 0.19/0.57      (![X6 : $i, X7 : $i]:
% 0.19/0.57         (~ (m1_pre_topc @ X6 @ X7)
% 0.19/0.57          | (v2_pre_topc @ X6)
% 0.19/0.57          | ~ (l1_pre_topc @ X7)
% 0.19/0.57          | ~ (v2_pre_topc @ X7))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.57  thf('65', plain,
% 0.19/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.57        | (v2_pre_topc @ sk_C_1))),
% 0.19/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.57  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('68', plain, ((v2_pre_topc @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.19/0.57  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.19/0.57      inference('demod', [status(thm)], ['32', '33', '34', '39'])).
% 0.19/0.57  thf('70', plain,
% 0.19/0.57      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['61', '62', '68', '69'])).
% 0.19/0.57  thf('71', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('72', plain,
% 0.19/0.57      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.19/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.57      inference('demod', [status(thm)], ['26', '71'])).
% 0.19/0.57  thf('73', plain,
% 0.19/0.57      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.19/0.57        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('74', plain, (((sk_F) = (sk_G))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('75', plain,
% 0.19/0.57      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.19/0.57        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.19/0.57      inference('demod', [status(thm)], ['73', '74'])).
% 0.19/0.57  thf('76', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_E @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('77', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('78', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_E @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.57  thf('79', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf(t83_tmap_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.57             ( l1_pre_topc @ B ) ) =>
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.57               ( ![D:$i]:
% 0.19/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.57                   ( ![E:$i]:
% 0.19/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.57                         ( v1_funct_2 @
% 0.19/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.57                         ( m1_subset_1 @
% 0.19/0.57                           E @ 
% 0.19/0.57                           ( k1_zfmisc_1 @
% 0.19/0.57                             ( k2_zfmisc_1 @
% 0.19/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.57                         ( ![F:$i]:
% 0.19/0.57                           ( ( m1_subset_1 @
% 0.19/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.19/0.57                             ( ![G:$i]:
% 0.19/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.57                                 ( ![H:$i]:
% 0.19/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.57                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.57                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.19/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.19/0.57                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.19/0.57                                         ( r1_tmap_1 @
% 0.19/0.57                                           C @ B @ 
% 0.19/0.57                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.19/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.57  thf('80', plain,
% 0.19/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.19/0.57         X31 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X24)
% 0.19/0.57          | ~ (v2_pre_topc @ X24)
% 0.19/0.57          | ~ (l1_pre_topc @ X24)
% 0.19/0.57          | (v2_struct_0 @ X25)
% 0.19/0.57          | ~ (m1_pre_topc @ X25 @ X26)
% 0.19/0.57          | ~ (m1_pre_topc @ X27 @ X25)
% 0.19/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.57          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.19/0.57          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.19/0.57               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.19/0.57          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X31)
% 0.19/0.57          | ((X31) != (X29))
% 0.19/0.57          | ~ (m1_connsp_2 @ X28 @ X25 @ X31)
% 0.19/0.57          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.19/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X25))
% 0.19/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.57               (k1_zfmisc_1 @ 
% 0.19/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.19/0.57          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.19/0.57          | ~ (v1_funct_1 @ X30)
% 0.19/0.57          | ~ (m1_pre_topc @ X27 @ X26)
% 0.19/0.57          | (v2_struct_0 @ X27)
% 0.19/0.57          | ~ (l1_pre_topc @ X26)
% 0.19/0.57          | ~ (v2_pre_topc @ X26)
% 0.19/0.57          | (v2_struct_0 @ X26))),
% 0.19/0.57      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.19/0.57  thf('81', plain,
% 0.19/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X26)
% 0.19/0.57          | ~ (v2_pre_topc @ X26)
% 0.19/0.57          | ~ (l1_pre_topc @ X26)
% 0.19/0.57          | (v2_struct_0 @ X27)
% 0.19/0.57          | ~ (m1_pre_topc @ X27 @ X26)
% 0.19/0.57          | ~ (v1_funct_1 @ X30)
% 0.19/0.57          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.19/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.57               (k1_zfmisc_1 @ 
% 0.19/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.19/0.57          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 0.19/0.57          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.19/0.57          | ~ (m1_connsp_2 @ X28 @ X25 @ X29)
% 0.19/0.57          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X29)
% 0.19/0.57          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.19/0.57               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.19/0.57          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.19/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.57          | ~ (m1_pre_topc @ X27 @ X25)
% 0.19/0.57          | ~ (m1_pre_topc @ X25 @ X26)
% 0.19/0.57          | (v2_struct_0 @ X25)
% 0.19/0.57          | ~ (l1_pre_topc @ X24)
% 0.19/0.57          | ~ (v2_pre_topc @ X24)
% 0.19/0.57          | (v2_struct_0 @ X24))),
% 0.19/0.57      inference('simplify', [status(thm)], ['80'])).
% 0.19/0.57  thf('82', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X1 @ 
% 0.19/0.57             (k1_zfmisc_1 @ 
% 0.19/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.19/0.57          | (v2_struct_0 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.19/0.57          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.19/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.57          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.19/0.57               X5)
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.19/0.57          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.19/0.57          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.19/0.57          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.19/0.57          | ~ (v1_funct_1 @ X1)
% 0.19/0.57          | ~ (m1_pre_topc @ X3 @ X2)
% 0.19/0.57          | (v2_struct_0 @ X3)
% 0.19/0.57          | ~ (l1_pre_topc @ X2)
% 0.19/0.57          | ~ (v2_pre_topc @ X2)
% 0.19/0.57          | (v2_struct_0 @ X2))),
% 0.19/0.57      inference('sup-', [status(thm)], ['79', '81'])).
% 0.19/0.57  thf('83', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('84', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('85', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('86', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X1 @ 
% 0.19/0.57             (k1_zfmisc_1 @ 
% 0.19/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.19/0.57          | (v2_struct_0 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.19/0.57          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.19/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.57          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.19/0.57               X5)
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.19/0.57          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.19/0.57          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.19/0.57          | ~ (v1_funct_1 @ X1)
% 0.19/0.57          | ~ (m1_pre_topc @ X3 @ X2)
% 0.19/0.57          | (v2_struct_0 @ X3)
% 0.19/0.57          | ~ (l1_pre_topc @ X2)
% 0.19/0.57          | ~ (v2_pre_topc @ X2)
% 0.19/0.57          | (v2_struct_0 @ X2))),
% 0.19/0.57      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.19/0.57  thf('87', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | (v2_struct_0 @ X1)
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.19/0.57               (u1_struct_0 @ sk_B))
% 0.19/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.19/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.19/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.19/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.57          | (v2_struct_0 @ sk_B))),
% 0.19/0.57      inference('sup-', [status(thm)], ['78', '86'])).
% 0.19/0.57  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('89', plain,
% 0.19/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('90', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('91', plain,
% 0.19/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.19/0.57      inference('demod', [status(thm)], ['89', '90'])).
% 0.19/0.57  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('94', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X0)
% 0.19/0.57          | ~ (v2_pre_topc @ X0)
% 0.19/0.57          | ~ (l1_pre_topc @ X0)
% 0.19/0.57          | (v2_struct_0 @ X1)
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.19/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.19/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.19/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | (v2_struct_0 @ sk_B))),
% 0.19/0.57      inference('demod', [status(thm)], ['87', '88', '91', '92', '93'])).
% 0.19/0.57  thf('95', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((v2_struct_0 @ sk_B)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.19/0.57          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.19/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.19/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.19/0.57          | (v2_struct_0 @ sk_C_1)
% 0.19/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.57          | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['75', '94'])).
% 0.19/0.57  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('97', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.57  thf('98', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('99', plain, (((sk_F) = (sk_G))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('100', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('demod', [status(thm)], ['98', '99'])).
% 0.19/0.57  thf('101', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('demod', [status(thm)], ['98', '99'])).
% 0.19/0.57  thf('102', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('105', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((v2_struct_0 @ sk_B)
% 0.19/0.57          | (v2_struct_0 @ sk_D)
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.19/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.19/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57          | (v2_struct_0 @ sk_C_1)
% 0.19/0.57          | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)],
% 0.19/0.57                ['95', '96', '97', '100', '101', '102', '103', '104'])).
% 0.19/0.57  thf('106', plain,
% 0.19/0.57      (((v2_struct_0 @ sk_A)
% 0.19/0.57        | (v2_struct_0 @ sk_C_1)
% 0.19/0.57        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.19/0.57        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.19/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.19/0.57        | (v2_struct_0 @ sk_D)
% 0.19/0.57        | (v2_struct_0 @ sk_B))),
% 0.19/0.57      inference('sup-', [status(thm)], ['72', '105'])).
% 0.19/0.57  thf('107', plain,
% 0.19/0.57      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.19/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['17', '25'])).
% 0.19/0.57  thf(t3_subset, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.57  thf('108', plain,
% 0.19/0.57      (![X3 : $i, X4 : $i]:
% 0.19/0.57         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.57  thf('109', plain,
% 0.19/0.57      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.57  thf('110', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.19/0.57      inference('demod', [status(thm)], ['58', '70'])).
% 0.19/0.57  thf('111', plain,
% 0.19/0.57      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('demod', [status(thm)], ['109', '110'])).
% 0.19/0.57  thf('112', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.19/0.57      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.57  thf('113', plain,
% 0.19/0.57      (((v2_struct_0 @ sk_A)
% 0.19/0.57        | (v2_struct_0 @ sk_C_1)
% 0.19/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.19/0.57        | (v2_struct_0 @ sk_D)
% 0.19/0.57        | (v2_struct_0 @ sk_B))),
% 0.19/0.57      inference('demod', [status(thm)], ['106', '111', '112'])).
% 0.19/0.57  thf('114', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('115', plain,
% 0.19/0.57      (((v2_struct_0 @ sk_B)
% 0.19/0.57        | (v2_struct_0 @ sk_D)
% 0.19/0.57        | (v2_struct_0 @ sk_C_1)
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.19/0.57  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('117', plain,
% 0.19/0.57      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.19/0.57      inference('sup-', [status(thm)], ['115', '116'])).
% 0.19/0.57  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('119', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.19/0.57      inference('clc', [status(thm)], ['117', '118'])).
% 0.19/0.57  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('121', plain, ((v2_struct_0 @ sk_C_1)),
% 0.19/0.57      inference('clc', [status(thm)], ['119', '120'])).
% 0.19/0.57  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
