%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.InMsh7IZgC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:27 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  172 (1967 expanded)
%              Number of leaves         :   38 ( 577 expanded)
%              Depth                    :   26
%              Number of atoms          : 1756 (58555 expanded)
%              Number of equality atoms :   37 (1626 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_connsp_2 @ ( sk_C @ X20 @ X19 ) @ X19 @ X20 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X16 @ X17 ) ) ),
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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i] :
      ( ~ ( v1_pre_topc @ X6 )
      | ( X6
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ( m1_pre_topc @ X13 @ X12 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('37',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['34','45','46','47','48','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('53',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('58',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('62',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X6: $i] :
      ( ~ ( v1_pre_topc @ X6 )
      | ( X6
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( m1_pre_topc @ X2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['43','44'])).

thf('69',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('71',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('72',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('76',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('77',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('81',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','82'])).

thf('84',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','83'])).

thf('85',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

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

thf('92',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X34 )
      | ( X34 != X32 )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X34 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_connsp_2 @ X31 @ X28 @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
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
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('98',plain,(
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
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
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
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','81'])).

thf('103',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
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
    inference(demod,[status(thm)],['99','100','103','104','105'])).

thf('107',plain,(
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
    inference('sup-',[status(thm)],['87','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('110',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('114',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109','112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','117'])).

thf('119',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','83'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('120',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('121',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('124',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.InMsh7IZgC
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.67/1.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.67/1.90  % Solved by: fo/fo7.sh
% 1.67/1.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.67/1.90  % done 1276 iterations in 1.456s
% 1.67/1.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.67/1.90  % SZS output start Refutation
% 1.67/1.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.67/1.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.67/1.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.67/1.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.67/1.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.67/1.90  thf(sk_B_type, type, sk_B: $i).
% 1.67/1.90  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.67/1.90  thf(sk_A_type, type, sk_A: $i).
% 1.67/1.90  thf(sk_E_type, type, sk_E: $i).
% 1.67/1.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.67/1.90  thf(sk_F_type, type, sk_F: $i).
% 1.67/1.90  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.67/1.90  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.67/1.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.67/1.90  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.67/1.90  thf(sk_D_type, type, sk_D: $i).
% 1.67/1.90  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.67/1.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.67/1.90  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.67/1.90  thf(sk_G_type, type, sk_G: $i).
% 1.67/1.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.67/1.90  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.67/1.90  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.67/1.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.67/1.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.67/1.90  thf(t88_tmap_1, conjecture,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.67/1.90       ( ![B:$i]:
% 1.67/1.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.67/1.90             ( l1_pre_topc @ B ) ) =>
% 1.67/1.90           ( ![C:$i]:
% 1.67/1.90             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.67/1.90               ( ![D:$i]:
% 1.67/1.90                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.67/1.90                   ( ![E:$i]:
% 1.67/1.90                     ( ( ( v1_funct_1 @ E ) & 
% 1.67/1.90                         ( v1_funct_2 @
% 1.67/1.90                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.67/1.90                         ( m1_subset_1 @
% 1.67/1.90                           E @ 
% 1.67/1.90                           ( k1_zfmisc_1 @
% 1.67/1.90                             ( k2_zfmisc_1 @
% 1.67/1.90                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.67/1.90                       ( ( ( g1_pre_topc @
% 1.67/1.90                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.67/1.90                           ( D ) ) =>
% 1.67/1.90                         ( ![F:$i]:
% 1.67/1.90                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.67/1.90                             ( ![G:$i]:
% 1.67/1.90                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.67/1.90                                 ( ( ( ( F ) = ( G ) ) & 
% 1.67/1.90                                     ( r1_tmap_1 @
% 1.67/1.90                                       C @ B @ 
% 1.67/1.90                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.67/1.90                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.67/1.90  thf(zf_stmt_0, negated_conjecture,
% 1.67/1.90    (~( ![A:$i]:
% 1.67/1.90        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.67/1.90            ( l1_pre_topc @ A ) ) =>
% 1.67/1.90          ( ![B:$i]:
% 1.67/1.90            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.67/1.90                ( l1_pre_topc @ B ) ) =>
% 1.67/1.90              ( ![C:$i]:
% 1.67/1.90                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.67/1.90                  ( ![D:$i]:
% 1.67/1.90                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.67/1.90                      ( ![E:$i]:
% 1.67/1.90                        ( ( ( v1_funct_1 @ E ) & 
% 1.67/1.90                            ( v1_funct_2 @
% 1.67/1.90                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.67/1.90                            ( m1_subset_1 @
% 1.67/1.90                              E @ 
% 1.67/1.90                              ( k1_zfmisc_1 @
% 1.67/1.90                                ( k2_zfmisc_1 @
% 1.67/1.90                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.67/1.90                          ( ( ( g1_pre_topc @
% 1.67/1.90                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.67/1.90                              ( D ) ) =>
% 1.67/1.90                            ( ![F:$i]:
% 1.67/1.90                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.67/1.90                                ( ![G:$i]:
% 1.67/1.90                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.67/1.90                                    ( ( ( ( F ) = ( G ) ) & 
% 1.67/1.90                                        ( r1_tmap_1 @
% 1.67/1.90                                          C @ B @ 
% 1.67/1.90                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.67/1.90                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.67/1.90    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.67/1.90  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(existence_m1_connsp_2, axiom,
% 1.67/1.90    (![A:$i,B:$i]:
% 1.67/1.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.67/1.90         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.90       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 1.67/1.90  thf('2', plain,
% 1.67/1.90      (![X19 : $i, X20 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X19)
% 1.67/1.90          | ~ (v2_pre_topc @ X19)
% 1.67/1.90          | (v2_struct_0 @ X19)
% 1.67/1.90          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 1.67/1.90          | (m1_connsp_2 @ (sk_C @ X20 @ X19) @ X19 @ X20))),
% 1.67/1.90      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 1.67/1.90  thf('3', plain,
% 1.67/1.90      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 1.67/1.90        | (v2_struct_0 @ sk_D)
% 1.67/1.90        | ~ (v2_pre_topc @ sk_D)
% 1.67/1.90        | ~ (l1_pre_topc @ sk_D))),
% 1.67/1.90      inference('sup-', [status(thm)], ['1', '2'])).
% 1.67/1.90  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(cc1_pre_topc, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.67/1.90       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.67/1.90  thf('5', plain,
% 1.67/1.90      (![X7 : $i, X8 : $i]:
% 1.67/1.90         (~ (m1_pre_topc @ X7 @ X8)
% 1.67/1.90          | (v2_pre_topc @ X7)
% 1.67/1.90          | ~ (l1_pre_topc @ X8)
% 1.67/1.90          | ~ (v2_pre_topc @ X8))),
% 1.67/1.90      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.67/1.90  thf('6', plain,
% 1.67/1.90      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.67/1.90      inference('sup-', [status(thm)], ['4', '5'])).
% 1.67/1.90  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.67/1.90  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(dt_m1_pre_topc, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( l1_pre_topc @ A ) =>
% 1.67/1.90       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.67/1.90  thf('11', plain,
% 1.67/1.90      (![X9 : $i, X10 : $i]:
% 1.67/1.90         (~ (m1_pre_topc @ X9 @ X10)
% 1.67/1.90          | (l1_pre_topc @ X9)
% 1.67/1.90          | ~ (l1_pre_topc @ X10))),
% 1.67/1.90      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.67/1.90  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.67/1.90      inference('sup-', [status(thm)], ['10', '11'])).
% 1.67/1.90  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('15', plain,
% 1.67/1.90      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 1.67/1.90        | (v2_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['3', '9', '14'])).
% 1.67/1.90  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 1.67/1.90      inference('clc', [status(thm)], ['15', '16'])).
% 1.67/1.90  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(dt_m1_connsp_2, axiom,
% 1.67/1.90    (![A:$i,B:$i]:
% 1.67/1.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.67/1.90         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.67/1.90       ( ![C:$i]:
% 1.67/1.90         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 1.67/1.90           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.67/1.90  thf('19', plain,
% 1.67/1.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X16)
% 1.67/1.90          | ~ (v2_pre_topc @ X16)
% 1.67/1.90          | (v2_struct_0 @ X16)
% 1.67/1.90          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 1.67/1.90          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.67/1.90          | ~ (m1_connsp_2 @ X18 @ X16 @ X17))),
% 1.67/1.90      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 1.67/1.90  thf('20', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.67/1.90          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (v2_pre_topc @ sk_D)
% 1.67/1.90          | ~ (l1_pre_topc @ sk_D))),
% 1.67/1.90      inference('sup-', [status(thm)], ['18', '19'])).
% 1.67/1.90  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.67/1.90  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('23', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.67/1.90          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.67/1.90          | (v2_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.67/1.90  thf('24', plain, (~ (v2_struct_0 @ sk_D)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('25', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.67/1.90          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 1.67/1.90      inference('clc', [status(thm)], ['23', '24'])).
% 1.67/1.90  thf(t2_tsep_1, axiom,
% 1.67/1.90    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.67/1.90  thf('26', plain,
% 1.67/1.90      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 1.67/1.90      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.67/1.90  thf('27', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(abstractness_v1_pre_topc, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( l1_pre_topc @ A ) =>
% 1.67/1.90       ( ( v1_pre_topc @ A ) =>
% 1.67/1.90         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.67/1.90  thf('28', plain,
% 1.67/1.90      (![X6 : $i]:
% 1.67/1.90         (~ (v1_pre_topc @ X6)
% 1.67/1.90          | ((X6) = (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.67/1.90          | ~ (l1_pre_topc @ X6))),
% 1.67/1.90      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.67/1.90  thf(t31_pre_topc, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( l1_pre_topc @ A ) =>
% 1.67/1.90       ( ![B:$i]:
% 1.67/1.90         ( ( l1_pre_topc @ B ) =>
% 1.67/1.90           ( ![C:$i]:
% 1.67/1.90             ( ( l1_pre_topc @ C ) =>
% 1.67/1.90               ( ![D:$i]:
% 1.67/1.90                 ( ( l1_pre_topc @ D ) =>
% 1.67/1.90                   ( ( ( ( g1_pre_topc @
% 1.67/1.90                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.67/1.90                         ( g1_pre_topc @
% 1.67/1.90                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.67/1.90                       ( ( g1_pre_topc @
% 1.67/1.90                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.67/1.90                         ( g1_pre_topc @
% 1.67/1.90                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 1.67/1.90                       ( m1_pre_topc @ C @ A ) ) =>
% 1.67/1.90                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.67/1.90  thf('29', plain,
% 1.67/1.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X12)
% 1.67/1.90          | ~ (l1_pre_topc @ X13)
% 1.67/1.90          | (m1_pre_topc @ X13 @ X12)
% 1.67/1.90          | ((g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14))
% 1.67/1.90              != (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 1.67/1.90          | ~ (m1_pre_topc @ X14 @ X15)
% 1.67/1.90          | ((g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))
% 1.67/1.90              != (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 1.67/1.90          | ~ (l1_pre_topc @ X14)
% 1.67/1.90          | ~ (l1_pre_topc @ X15))),
% 1.67/1.90      inference('cnf', [status(esa)], [t31_pre_topc])).
% 1.67/1.90  thf('30', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.67/1.90              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ X0)
% 1.67/1.90          | (m1_pre_topc @ X1 @ X2)
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X2))),
% 1.67/1.90      inference('eq_res', [status(thm)], ['29'])).
% 1.67/1.90  thf('31', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X2)
% 1.67/1.90          | (m1_pre_topc @ X1 @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ X0)
% 1.67/1.90          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.67/1.90              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X0))),
% 1.67/1.90      inference('simplify', [status(thm)], ['30'])).
% 1.67/1.90  thf('32', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.90         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (v1_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X2 @ X0)
% 1.67/1.90          | (m1_pre_topc @ X2 @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X1))),
% 1.67/1.90      inference('sup-', [status(thm)], ['28', '31'])).
% 1.67/1.90  thf('33', plain,
% 1.67/1.90      (![X1 : $i, X2 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X1)
% 1.67/1.90          | (m1_pre_topc @ X2 @ X1)
% 1.67/1.90          | ~ (m1_pre_topc @ X2 @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (v1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.67/1.90          | ~ (l1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 1.67/1.90      inference('simplify', [status(thm)], ['32'])).
% 1.67/1.90  thf('34', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (v1_pre_topc @ sk_D)
% 1.67/1.90          | ~ (l1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (m1_pre_topc @ X0 @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 1.67/1.90          | (m1_pre_topc @ X0 @ sk_C_1)
% 1.67/1.90          | ~ (l1_pre_topc @ sk_C_1))),
% 1.67/1.90      inference('sup-', [status(thm)], ['27', '33'])).
% 1.67/1.90  thf('35', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf(fc7_pre_topc, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.67/1.90       ( ( ~( v2_struct_0 @
% 1.67/1.90              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 1.67/1.90         ( v1_pre_topc @
% 1.67/1.90           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.67/1.90  thf('36', plain,
% 1.67/1.90      (![X11 : $i]:
% 1.67/1.90         ((v1_pre_topc @ 
% 1.67/1.90           (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 1.67/1.90          | ~ (l1_pre_topc @ X11)
% 1.67/1.90          | (v2_struct_0 @ X11))),
% 1.67/1.90      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 1.67/1.90  thf('37', plain,
% 1.67/1.90      (((v1_pre_topc @ sk_D)
% 1.67/1.90        | (v2_struct_0 @ sk_C_1)
% 1.67/1.90        | ~ (l1_pre_topc @ sk_C_1))),
% 1.67/1.90      inference('sup+', [status(thm)], ['35', '36'])).
% 1.67/1.90  thf('38', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('39', plain,
% 1.67/1.90      (![X9 : $i, X10 : $i]:
% 1.67/1.90         (~ (m1_pre_topc @ X9 @ X10)
% 1.67/1.90          | (l1_pre_topc @ X9)
% 1.67/1.90          | ~ (l1_pre_topc @ X10))),
% 1.67/1.90      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.67/1.90  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 1.67/1.90      inference('sup-', [status(thm)], ['38', '39'])).
% 1.67/1.90  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('43', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('demod', [status(thm)], ['37', '42'])).
% 1.67/1.90  thf('44', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('45', plain, ((v1_pre_topc @ sk_D)),
% 1.67/1.90      inference('clc', [status(thm)], ['43', '44'])).
% 1.67/1.90  thf('46', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('48', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('49', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('50', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.67/1.90          | (m1_pre_topc @ X0 @ sk_C_1))),
% 1.67/1.90      inference('demod', [status(thm)], ['34', '45', '46', '47', '48', '49'])).
% 1.67/1.90  thf('51', plain,
% 1.67/1.90      ((~ (l1_pre_topc @ sk_D)
% 1.67/1.90        | (m1_pre_topc @ sk_D @ sk_C_1)
% 1.67/1.90        | ~ (l1_pre_topc @ sk_D))),
% 1.67/1.90      inference('sup-', [status(thm)], ['26', '50'])).
% 1.67/1.90  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.67/1.90  thf(t35_borsuk_1, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( l1_pre_topc @ A ) =>
% 1.67/1.90       ( ![B:$i]:
% 1.67/1.90         ( ( m1_pre_topc @ B @ A ) =>
% 1.67/1.90           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.67/1.90  thf('55', plain,
% 1.67/1.90      (![X22 : $i, X23 : $i]:
% 1.67/1.90         (~ (m1_pre_topc @ X22 @ X23)
% 1.67/1.90          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 1.67/1.90          | ~ (l1_pre_topc @ X23))),
% 1.67/1.90      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.67/1.90  thf('56', plain,
% 1.67/1.90      ((~ (l1_pre_topc @ sk_C_1)
% 1.67/1.90        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 1.67/1.90      inference('sup-', [status(thm)], ['54', '55'])).
% 1.67/1.90  thf('57', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('58', plain,
% 1.67/1.90      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('demod', [status(thm)], ['56', '57'])).
% 1.67/1.90  thf(d10_xboole_0, axiom,
% 1.67/1.90    (![A:$i,B:$i]:
% 1.67/1.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.67/1.90  thf('59', plain,
% 1.67/1.90      (![X0 : $i, X2 : $i]:
% 1.67/1.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.67/1.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.67/1.90  thf('60', plain,
% 1.67/1.90      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 1.67/1.90        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 1.67/1.90      inference('sup-', [status(thm)], ['58', '59'])).
% 1.67/1.90  thf('61', plain,
% 1.67/1.90      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 1.67/1.90      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.67/1.90  thf('62', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('63', plain,
% 1.67/1.90      (![X6 : $i]:
% 1.67/1.90         (~ (v1_pre_topc @ X6)
% 1.67/1.90          | ((X6) = (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.67/1.90          | ~ (l1_pre_topc @ X6))),
% 1.67/1.90      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.67/1.90  thf('64', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X2)
% 1.67/1.90          | (m1_pre_topc @ X1 @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ X0)
% 1.67/1.90          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.67/1.90              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X0))),
% 1.67/1.90      inference('simplify', [status(thm)], ['30'])).
% 1.67/1.90  thf('65', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.67/1.90         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (v1_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X2 @ X1)
% 1.67/1.90          | (m1_pre_topc @ X2 @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0))),
% 1.67/1.90      inference('sup-', [status(thm)], ['63', '64'])).
% 1.67/1.90  thf('66', plain,
% 1.67/1.90      (![X1 : $i, X2 : $i]:
% 1.67/1.90         ((m1_pre_topc @ X2 @ 
% 1.67/1.90           (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.67/1.90          | ~ (m1_pre_topc @ X2 @ X1)
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (l1_pre_topc @ X1)
% 1.67/1.90          | ~ (v1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.67/1.90          | ~ (l1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 1.67/1.90      inference('simplify', [status(thm)], ['65'])).
% 1.67/1.90  thf('67', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (v1_pre_topc @ sk_D)
% 1.67/1.90          | ~ (l1_pre_topc @ 
% 1.67/1.90               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 1.67/1.90          | ~ (l1_pre_topc @ sk_C_1)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.67/1.90          | (m1_pre_topc @ X0 @ 
% 1.67/1.90             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))),
% 1.67/1.90      inference('sup-', [status(thm)], ['62', '66'])).
% 1.67/1.90  thf('68', plain, ((v1_pre_topc @ sk_D)),
% 1.67/1.90      inference('clc', [status(thm)], ['43', '44'])).
% 1.67/1.90  thf('69', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('70', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('71', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('72', plain,
% 1.67/1.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.67/1.90         = (sk_D))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('73', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         (~ (l1_pre_topc @ X0)
% 1.67/1.90          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 1.67/1.90          | (m1_pre_topc @ X0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 1.67/1.90  thf('74', plain,
% 1.67/1.90      ((~ (l1_pre_topc @ sk_C_1)
% 1.67/1.90        | (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.67/1.90        | ~ (l1_pre_topc @ sk_C_1))),
% 1.67/1.90      inference('sup-', [status(thm)], ['61', '73'])).
% 1.67/1.90  thf('75', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('76', plain, ((l1_pre_topc @ sk_C_1)),
% 1.67/1.90      inference('demod', [status(thm)], ['40', '41'])).
% 1.67/1.90  thf('77', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.67/1.90  thf('78', plain,
% 1.67/1.90      (![X22 : $i, X23 : $i]:
% 1.67/1.90         (~ (m1_pre_topc @ X22 @ X23)
% 1.67/1.90          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 1.67/1.90          | ~ (l1_pre_topc @ X23))),
% 1.67/1.90      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.67/1.90  thf('79', plain,
% 1.67/1.90      ((~ (l1_pre_topc @ sk_D)
% 1.67/1.90        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 1.67/1.90      inference('sup-', [status(thm)], ['77', '78'])).
% 1.67/1.90  thf('80', plain, ((l1_pre_topc @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['12', '13'])).
% 1.67/1.90  thf('81', plain,
% 1.67/1.90      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['79', '80'])).
% 1.67/1.90  thf('82', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('83', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 1.67/1.90      inference('demod', [status(thm)], ['25', '82'])).
% 1.67/1.90  thf('84', plain,
% 1.67/1.90      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 1.67/1.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 1.67/1.90      inference('sup-', [status(thm)], ['17', '83'])).
% 1.67/1.90  thf('85', plain,
% 1.67/1.90      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 1.67/1.90        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('86', plain, (((sk_F) = (sk_G))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('87', plain,
% 1.67/1.90      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 1.67/1.90        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 1.67/1.90      inference('demod', [status(thm)], ['85', '86'])).
% 1.67/1.90  thf('88', plain,
% 1.67/1.90      ((m1_subset_1 @ sk_E @ 
% 1.67/1.90        (k1_zfmisc_1 @ 
% 1.67/1.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('89', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('90', plain,
% 1.67/1.90      ((m1_subset_1 @ sk_E @ 
% 1.67/1.90        (k1_zfmisc_1 @ 
% 1.67/1.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.67/1.90      inference('demod', [status(thm)], ['88', '89'])).
% 1.67/1.90  thf('91', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf(t83_tmap_1, axiom,
% 1.67/1.90    (![A:$i]:
% 1.67/1.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.67/1.90       ( ![B:$i]:
% 1.67/1.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.67/1.90             ( l1_pre_topc @ B ) ) =>
% 1.67/1.90           ( ![C:$i]:
% 1.67/1.90             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.67/1.90               ( ![D:$i]:
% 1.67/1.90                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.67/1.90                   ( ![E:$i]:
% 1.67/1.90                     ( ( ( v1_funct_1 @ E ) & 
% 1.67/1.90                         ( v1_funct_2 @
% 1.67/1.90                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.67/1.90                         ( m1_subset_1 @
% 1.67/1.90                           E @ 
% 1.67/1.90                           ( k1_zfmisc_1 @
% 1.67/1.90                             ( k2_zfmisc_1 @
% 1.67/1.90                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.67/1.90                       ( ( m1_pre_topc @ C @ D ) =>
% 1.67/1.90                         ( ![F:$i]:
% 1.67/1.90                           ( ( m1_subset_1 @
% 1.67/1.90                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 1.67/1.90                             ( ![G:$i]:
% 1.67/1.90                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 1.67/1.90                                 ( ![H:$i]:
% 1.67/1.90                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 1.67/1.90                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 1.67/1.90                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 1.67/1.90                                         ( ( G ) = ( H ) ) ) =>
% 1.67/1.90                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 1.67/1.90                                         ( r1_tmap_1 @
% 1.67/1.90                                           C @ B @ 
% 1.67/1.90                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 1.67/1.90                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.67/1.90  thf('92', plain,
% 1.67/1.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 1.67/1.90         X34 : $i]:
% 1.67/1.90         ((v2_struct_0 @ X27)
% 1.67/1.90          | ~ (v2_pre_topc @ X27)
% 1.67/1.90          | ~ (l1_pre_topc @ X27)
% 1.67/1.90          | (v2_struct_0 @ X28)
% 1.67/1.90          | ~ (m1_pre_topc @ X28 @ X29)
% 1.67/1.90          | ~ (m1_pre_topc @ X30 @ X28)
% 1.67/1.90          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.67/1.90          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 1.67/1.90          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 1.67/1.90               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 1.67/1.90          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X34)
% 1.67/1.90          | ((X34) != (X32))
% 1.67/1.90          | ~ (m1_connsp_2 @ X31 @ X28 @ X34)
% 1.67/1.90          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 1.67/1.90          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X28))
% 1.67/1.90          | ~ (m1_subset_1 @ X33 @ 
% 1.67/1.90               (k1_zfmisc_1 @ 
% 1.67/1.90                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 1.67/1.90          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.67/1.90          | ~ (v1_funct_1 @ X33)
% 1.67/1.90          | ~ (m1_pre_topc @ X30 @ X29)
% 1.67/1.90          | (v2_struct_0 @ X30)
% 1.67/1.90          | ~ (l1_pre_topc @ X29)
% 1.67/1.90          | ~ (v2_pre_topc @ X29)
% 1.67/1.90          | (v2_struct_0 @ X29))),
% 1.67/1.90      inference('cnf', [status(esa)], [t83_tmap_1])).
% 1.67/1.90  thf('93', plain,
% 1.67/1.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.67/1.90         ((v2_struct_0 @ X29)
% 1.67/1.90          | ~ (v2_pre_topc @ X29)
% 1.67/1.90          | ~ (l1_pre_topc @ X29)
% 1.67/1.90          | (v2_struct_0 @ X30)
% 1.67/1.90          | ~ (m1_pre_topc @ X30 @ X29)
% 1.67/1.90          | ~ (v1_funct_1 @ X33)
% 1.67/1.90          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 1.67/1.90          | ~ (m1_subset_1 @ X33 @ 
% 1.67/1.90               (k1_zfmisc_1 @ 
% 1.67/1.90                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 1.67/1.90          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 1.67/1.90          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 1.67/1.90          | ~ (m1_connsp_2 @ X31 @ X28 @ X32)
% 1.67/1.90          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 1.67/1.90          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 1.67/1.90               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 1.67/1.90          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 1.67/1.90          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.67/1.90          | ~ (m1_pre_topc @ X30 @ X28)
% 1.67/1.90          | ~ (m1_pre_topc @ X28 @ X29)
% 1.67/1.90          | (v2_struct_0 @ X28)
% 1.67/1.90          | ~ (l1_pre_topc @ X27)
% 1.67/1.90          | ~ (v2_pre_topc @ X27)
% 1.67/1.90          | (v2_struct_0 @ X27))),
% 1.67/1.90      inference('simplify', [status(thm)], ['92'])).
% 1.67/1.90  thf('94', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.67/1.90         (~ (m1_subset_1 @ X1 @ 
% 1.67/1.90             (k1_zfmisc_1 @ 
% 1.67/1.90              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 1.67/1.90          | (v2_struct_0 @ X0)
% 1.67/1.90          | ~ (v2_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.67/1.90          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.67/1.90          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 1.67/1.90          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.67/1.90               X5)
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 1.67/1.90          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 1.67/1.90          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 1.67/1.90          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 1.67/1.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.67/1.90          | ~ (v1_funct_1 @ X1)
% 1.67/1.90          | ~ (m1_pre_topc @ X3 @ X2)
% 1.67/1.90          | (v2_struct_0 @ X3)
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (v2_pre_topc @ X2)
% 1.67/1.90          | (v2_struct_0 @ X2))),
% 1.67/1.90      inference('sup-', [status(thm)], ['91', '93'])).
% 1.67/1.90  thf('95', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('96', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('97', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('98', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.67/1.90         (~ (m1_subset_1 @ X1 @ 
% 1.67/1.90             (k1_zfmisc_1 @ 
% 1.67/1.90              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 1.67/1.90          | (v2_struct_0 @ X0)
% 1.67/1.90          | ~ (v2_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.67/1.90          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.67/1.90          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 1.67/1.90          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.67/1.90               X5)
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 1.67/1.90          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 1.67/1.90          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 1.67/1.90          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 1.67/1.90          | ~ (v1_funct_1 @ X1)
% 1.67/1.90          | ~ (m1_pre_topc @ X3 @ X2)
% 1.67/1.90          | (v2_struct_0 @ X3)
% 1.67/1.90          | ~ (l1_pre_topc @ X2)
% 1.67/1.90          | ~ (v2_pre_topc @ X2)
% 1.67/1.90          | (v2_struct_0 @ X2))),
% 1.67/1.90      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 1.67/1.90  thf('99', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.90         ((v2_struct_0 @ X0)
% 1.67/1.90          | ~ (v2_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | (v2_struct_0 @ X1)
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ X0)
% 1.67/1.90          | ~ (v1_funct_1 @ sk_E)
% 1.67/1.90          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 1.67/1.90               (u1_struct_0 @ sk_B))
% 1.67/1.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 1.67/1.90          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.67/1.90          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.67/1.90               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.67/1.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.67/1.90          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (l1_pre_topc @ sk_B)
% 1.67/1.90          | ~ (v2_pre_topc @ sk_B)
% 1.67/1.90          | (v2_struct_0 @ sk_B))),
% 1.67/1.90      inference('sup-', [status(thm)], ['90', '98'])).
% 1.67/1.90  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('101', plain,
% 1.67/1.90      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('102', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.67/1.90      inference('demod', [status(thm)], ['60', '81'])).
% 1.67/1.90  thf('103', plain,
% 1.67/1.90      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.67/1.90      inference('demod', [status(thm)], ['101', '102'])).
% 1.67/1.90  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('105', plain, ((v2_pre_topc @ sk_B)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('106', plain,
% 1.67/1.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.67/1.90         ((v2_struct_0 @ X0)
% 1.67/1.90          | ~ (v2_pre_topc @ X0)
% 1.67/1.90          | ~ (l1_pre_topc @ X0)
% 1.67/1.90          | (v2_struct_0 @ X1)
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ X0)
% 1.67/1.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 1.67/1.90          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.67/1.90          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.67/1.90               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.67/1.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.67/1.90          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | (v2_struct_0 @ sk_B))),
% 1.67/1.90      inference('demod', [status(thm)], ['99', '100', '103', '104', '105'])).
% 1.67/1.90  thf('107', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         ((v2_struct_0 @ sk_B)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.67/1.90          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.67/1.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.67/1.90          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.67/1.90          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 1.67/1.90          | (v2_struct_0 @ sk_C_1)
% 1.67/1.90          | ~ (l1_pre_topc @ sk_A)
% 1.67/1.90          | ~ (v2_pre_topc @ sk_A)
% 1.67/1.90          | (v2_struct_0 @ sk_A))),
% 1.67/1.90      inference('sup-', [status(thm)], ['87', '106'])).
% 1.67/1.90  thf('108', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('109', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.67/1.90      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.67/1.90  thf('110', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('111', plain, (((sk_F) = (sk_G))),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('112', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('demod', [status(thm)], ['110', '111'])).
% 1.67/1.90  thf('113', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('demod', [status(thm)], ['110', '111'])).
% 1.67/1.90  thf('114', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('117', plain,
% 1.67/1.90      (![X0 : $i]:
% 1.67/1.90         ((v2_struct_0 @ sk_B)
% 1.67/1.90          | (v2_struct_0 @ sk_D)
% 1.67/1.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 1.67/1.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.67/1.90          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.67/1.90          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90          | (v2_struct_0 @ sk_C_1)
% 1.67/1.90          | (v2_struct_0 @ sk_A))),
% 1.67/1.90      inference('demod', [status(thm)],
% 1.67/1.90                ['107', '108', '109', '112', '113', '114', '115', '116'])).
% 1.67/1.90  thf('118', plain,
% 1.67/1.90      (((v2_struct_0 @ sk_A)
% 1.67/1.90        | (v2_struct_0 @ sk_C_1)
% 1.67/1.90        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 1.67/1.90        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 1.67/1.90        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.67/1.90        | (v2_struct_0 @ sk_D)
% 1.67/1.90        | (v2_struct_0 @ sk_B))),
% 1.67/1.90      inference('sup-', [status(thm)], ['84', '117'])).
% 1.67/1.90  thf('119', plain,
% 1.67/1.90      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 1.67/1.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 1.67/1.90      inference('sup-', [status(thm)], ['17', '83'])).
% 1.67/1.90  thf(t3_subset, axiom,
% 1.67/1.90    (![A:$i,B:$i]:
% 1.67/1.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.67/1.90  thf('120', plain,
% 1.67/1.90      (![X3 : $i, X4 : $i]:
% 1.67/1.90         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 1.67/1.90      inference('cnf', [status(esa)], [t3_subset])).
% 1.67/1.90  thf('121', plain,
% 1.67/1.90      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('sup-', [status(thm)], ['119', '120'])).
% 1.67/1.90  thf('122', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 1.67/1.90      inference('clc', [status(thm)], ['15', '16'])).
% 1.67/1.90  thf('123', plain,
% 1.67/1.90      (((v2_struct_0 @ sk_A)
% 1.67/1.90        | (v2_struct_0 @ sk_C_1)
% 1.67/1.90        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.67/1.90        | (v2_struct_0 @ sk_D)
% 1.67/1.90        | (v2_struct_0 @ sk_B))),
% 1.67/1.90      inference('demod', [status(thm)], ['118', '121', '122'])).
% 1.67/1.90  thf('124', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('125', plain,
% 1.67/1.90      (((v2_struct_0 @ sk_B)
% 1.67/1.90        | (v2_struct_0 @ sk_D)
% 1.67/1.90        | (v2_struct_0 @ sk_C_1)
% 1.67/1.90        | (v2_struct_0 @ sk_A))),
% 1.67/1.90      inference('sup-', [status(thm)], ['123', '124'])).
% 1.67/1.90  thf('126', plain, (~ (v2_struct_0 @ sk_D)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('127', plain,
% 1.67/1.90      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 1.67/1.90      inference('sup-', [status(thm)], ['125', '126'])).
% 1.67/1.90  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 1.67/1.90      inference('clc', [status(thm)], ['127', '128'])).
% 1.67/1.90  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 1.67/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.90  thf('131', plain, ((v2_struct_0 @ sk_C_1)),
% 1.67/1.90      inference('clc', [status(thm)], ['129', '130'])).
% 1.67/1.90  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 1.67/1.90  
% 1.67/1.90  % SZS output end Refutation
% 1.67/1.90  
% 1.67/1.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
