%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iOgIumGLCr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:27 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  178 (1976 expanded)
%              Number of leaves         :   38 ( 581 expanded)
%              Depth                    :   23
%              Number of atoms          : 1733 (59792 expanded)
%              Number of equality atoms :   33 (1642 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( m1_pre_topc @ X2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ) ),
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

thf('48',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('49',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','45','46','47','48','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('53',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('54',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('61',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('63',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('68',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X6: $i] :
      ( ~ ( v1_pre_topc @ X6 )
      | ( X6
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['43','44'])).

thf('75',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('77',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78'])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['67','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('83',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','66','83'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('91',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('92',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('94',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','95'])).

thf('97',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','96'])).

thf('98',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('102',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X35 )
      | ( X35 != X33 )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X35 )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_connsp_2 @ X32 @ X29 @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','94'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['86','94'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('121',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('122',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','119','120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','123'])).

thf('125',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('126',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','96'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('127',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','128'])).

thf('130',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['0','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iOgIumGLCr
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.51/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.68  % Solved by: fo/fo7.sh
% 0.51/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.68  % done 421 iterations in 0.227s
% 0.51/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.68  % SZS output start Refutation
% 0.51/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.51/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.68  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.51/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.68  thf(sk_G_type, type, sk_G: $i).
% 0.51/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.68  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.51/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.68  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.51/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.51/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.68  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.51/0.68  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.51/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.51/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.68  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.51/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.68  thf(t88_tmap_1, conjecture,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.68             ( l1_pre_topc @ B ) ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.68               ( ![D:$i]:
% 0.51/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.68                   ( ![E:$i]:
% 0.51/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.68                         ( v1_funct_2 @
% 0.51/0.68                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.68                         ( m1_subset_1 @
% 0.51/0.68                           E @ 
% 0.51/0.68                           ( k1_zfmisc_1 @
% 0.51/0.68                             ( k2_zfmisc_1 @
% 0.51/0.68                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.68                       ( ( ( g1_pre_topc @
% 0.51/0.68                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.51/0.68                           ( D ) ) =>
% 0.51/0.68                         ( ![F:$i]:
% 0.51/0.68                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.68                             ( ![G:$i]:
% 0.51/0.68                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.68                                 ( ( ( ( F ) = ( G ) ) & 
% 0.51/0.68                                     ( r1_tmap_1 @
% 0.51/0.68                                       C @ B @ 
% 0.51/0.68                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.51/0.68                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.68    (~( ![A:$i]:
% 0.51/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.68            ( l1_pre_topc @ A ) ) =>
% 0.51/0.68          ( ![B:$i]:
% 0.51/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.68                ( l1_pre_topc @ B ) ) =>
% 0.51/0.68              ( ![C:$i]:
% 0.51/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.68                  ( ![D:$i]:
% 0.51/0.68                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.68                      ( ![E:$i]:
% 0.51/0.68                        ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.68                            ( v1_funct_2 @
% 0.51/0.68                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.68                            ( m1_subset_1 @
% 0.51/0.68                              E @ 
% 0.51/0.68                              ( k1_zfmisc_1 @
% 0.51/0.68                                ( k2_zfmisc_1 @
% 0.51/0.68                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.68                          ( ( ( g1_pre_topc @
% 0.51/0.68                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.51/0.68                              ( D ) ) =>
% 0.51/0.68                            ( ![F:$i]:
% 0.51/0.68                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.68                                ( ![G:$i]:
% 0.51/0.68                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.68                                    ( ( ( ( F ) = ( G ) ) & 
% 0.51/0.68                                        ( r1_tmap_1 @
% 0.51/0.68                                          C @ B @ 
% 0.51/0.68                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.51/0.68                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.68    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.51/0.68  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(existence_m1_connsp_2, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.68         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.68       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.51/0.68  thf('2', plain,
% 0.51/0.68      (![X19 : $i, X20 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X19)
% 0.51/0.68          | ~ (v2_pre_topc @ X19)
% 0.51/0.68          | (v2_struct_0 @ X19)
% 0.51/0.68          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.51/0.68          | (m1_connsp_2 @ (sk_C @ X20 @ X19) @ X19 @ X20))),
% 0.51/0.68      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.51/0.68  thf('3', plain,
% 0.51/0.68      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.51/0.68        | (v2_struct_0 @ sk_D)
% 0.51/0.68        | ~ (v2_pre_topc @ sk_D)
% 0.51/0.68        | ~ (l1_pre_topc @ sk_D))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(cc1_pre_topc, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.51/0.68  thf('5', plain,
% 0.51/0.68      (![X7 : $i, X8 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X7 @ X8)
% 0.51/0.68          | (v2_pre_topc @ X7)
% 0.51/0.68          | ~ (l1_pre_topc @ X8)
% 0.51/0.68          | ~ (v2_pre_topc @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.51/0.68  thf('6', plain,
% 0.51/0.68      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.51/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.68  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.51/0.68  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(dt_m1_pre_topc, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( l1_pre_topc @ A ) =>
% 0.51/0.68       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.51/0.68  thf('11', plain,
% 0.51/0.68      (![X9 : $i, X10 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X9 @ X10)
% 0.51/0.68          | (l1_pre_topc @ X9)
% 0.51/0.68          | ~ (l1_pre_topc @ X10))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.51/0.68  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.51/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.68  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('15', plain,
% 0.51/0.68      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.51/0.68        | (v2_struct_0 @ sk_D))),
% 0.51/0.68      inference('demod', [status(thm)], ['3', '9', '14'])).
% 0.51/0.68  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.51/0.68      inference('clc', [status(thm)], ['15', '16'])).
% 0.51/0.68  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(dt_m1_connsp_2, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.68         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.68       ( ![C:$i]:
% 0.51/0.68         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.51/0.68           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.51/0.68  thf('19', plain,
% 0.51/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X16)
% 0.51/0.68          | ~ (v2_pre_topc @ X16)
% 0.51/0.68          | (v2_struct_0 @ X16)
% 0.51/0.68          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.51/0.68          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.51/0.68          | ~ (m1_connsp_2 @ X18 @ X16 @ X17))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.51/0.68  thf('20', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.51/0.68          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | ~ (v2_pre_topc @ sk_D)
% 0.51/0.68          | ~ (l1_pre_topc @ sk_D))),
% 0.51/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.68  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.51/0.68  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('23', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.51/0.68          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.51/0.68          | (v2_struct_0 @ sk_D))),
% 0.51/0.68      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.51/0.68  thf('24', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('25', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.51/0.68          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.51/0.68      inference('clc', [status(thm)], ['23', '24'])).
% 0.51/0.68  thf(t2_tsep_1, axiom,
% 0.51/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.51/0.68  thf('26', plain,
% 0.51/0.68      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.68      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.68  thf('27', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(abstractness_v1_pre_topc, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( l1_pre_topc @ A ) =>
% 0.51/0.68       ( ( v1_pre_topc @ A ) =>
% 0.51/0.68         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.51/0.68  thf('28', plain,
% 0.51/0.68      (![X6 : $i]:
% 0.51/0.68         (~ (v1_pre_topc @ X6)
% 0.51/0.68          | ((X6) = (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.51/0.68          | ~ (l1_pre_topc @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.51/0.68  thf(t31_pre_topc, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( l1_pre_topc @ A ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( l1_pre_topc @ B ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( l1_pre_topc @ C ) =>
% 0.51/0.68               ( ![D:$i]:
% 0.51/0.68                 ( ( l1_pre_topc @ D ) =>
% 0.51/0.68                   ( ( ( ( g1_pre_topc @
% 0.51/0.68                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.51/0.68                         ( g1_pre_topc @
% 0.51/0.68                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.51/0.68                       ( ( g1_pre_topc @
% 0.51/0.68                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.51/0.68                         ( g1_pre_topc @
% 0.51/0.68                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.51/0.68                       ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.68                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.51/0.68  thf('29', plain,
% 0.51/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X12)
% 0.51/0.68          | ~ (l1_pre_topc @ X13)
% 0.51/0.68          | (m1_pre_topc @ X13 @ X12)
% 0.51/0.68          | ((g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14))
% 0.51/0.68              != (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.51/0.68          | ~ (m1_pre_topc @ X14 @ X15)
% 0.51/0.68          | ((g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))
% 0.51/0.68              != (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.51/0.68          | ~ (l1_pre_topc @ X14)
% 0.51/0.68          | ~ (l1_pre_topc @ X15))),
% 0.51/0.68      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.51/0.68  thf('30', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.51/0.68              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | (m1_pre_topc @ X1 @ X2)
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X2))),
% 0.51/0.68      inference('eq_res', [status(thm)], ['29'])).
% 0.51/0.68  thf('31', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X2)
% 0.51/0.68          | (m1_pre_topc @ X1 @ X2)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.51/0.68              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0))),
% 0.51/0.68      inference('simplify', [status(thm)], ['30'])).
% 0.51/0.68  thf('32', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v1_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X2)
% 0.51/0.68          | ~ (m1_pre_topc @ X2 @ X1)
% 0.51/0.68          | (m1_pre_topc @ X2 @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['28', '31'])).
% 0.51/0.68  thf('33', plain,
% 0.51/0.68      (![X1 : $i, X2 : $i]:
% 0.51/0.68         ((m1_pre_topc @ X2 @ 
% 0.51/0.68           (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.51/0.68          | ~ (m1_pre_topc @ X2 @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X2)
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ~ (v1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.51/0.68          | ~ (l1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['32'])).
% 0.51/0.68  thf('34', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (v1_pre_topc @ sk_D)
% 0.51/0.68          | ~ (l1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.51/0.68          | ~ (l1_pre_topc @ sk_C_1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.51/0.68          | (m1_pre_topc @ X0 @ 
% 0.51/0.68             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['27', '33'])).
% 0.51/0.68  thf('35', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(fc7_pre_topc, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ( ~( v2_struct_0 @
% 0.51/0.68              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.51/0.68         ( v1_pre_topc @
% 0.51/0.68           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.51/0.68  thf('36', plain,
% 0.51/0.68      (![X11 : $i]:
% 0.51/0.68         ((v1_pre_topc @ 
% 0.51/0.68           (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.51/0.68          | ~ (l1_pre_topc @ X11)
% 0.51/0.68          | (v2_struct_0 @ X11))),
% 0.51/0.68      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.51/0.68  thf('37', plain,
% 0.51/0.68      (((v1_pre_topc @ sk_D)
% 0.51/0.68        | (v2_struct_0 @ sk_C_1)
% 0.51/0.68        | ~ (l1_pre_topc @ sk_C_1))),
% 0.51/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.68  thf('38', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('39', plain,
% 0.51/0.68      (![X9 : $i, X10 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X9 @ X10)
% 0.51/0.68          | (l1_pre_topc @ X9)
% 0.51/0.68          | ~ (l1_pre_topc @ X10))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.51/0.68  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.68  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('43', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['37', '42'])).
% 0.51/0.68  thf('44', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('45', plain, ((v1_pre_topc @ sk_D)),
% 0.51/0.68      inference('clc', [status(thm)], ['43', '44'])).
% 0.51/0.68  thf('46', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('48', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('49', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('50', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.51/0.68          | (m1_pre_topc @ X0 @ sk_D))),
% 0.51/0.68      inference('demod', [status(thm)], ['34', '45', '46', '47', '48', '49'])).
% 0.51/0.68  thf('51', plain,
% 0.51/0.68      ((~ (l1_pre_topc @ sk_C_1)
% 0.51/0.68        | (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.51/0.68        | ~ (l1_pre_topc @ sk_C_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['26', '50'])).
% 0.51/0.68  thf('52', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('54', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.51/0.68  thf('55', plain,
% 0.51/0.68      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.68      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.68  thf(t4_tsep_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( m1_pre_topc @ C @ A ) =>
% 0.51/0.68               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.51/0.68                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.51/0.68  thf('56', plain,
% 0.51/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X22 @ X23)
% 0.51/0.68          | ~ (m1_pre_topc @ X22 @ X24)
% 0.51/0.68          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.51/0.68          | ~ (m1_pre_topc @ X24 @ X23)
% 0.51/0.68          | ~ (l1_pre_topc @ X23)
% 0.51/0.68          | ~ (v2_pre_topc @ X23))),
% 0.51/0.68      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.51/0.68  thf('57', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.68  thf('58', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.68          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X0))),
% 0.51/0.68      inference('simplify', [status(thm)], ['57'])).
% 0.51/0.68  thf('59', plain,
% 0.51/0.68      ((~ (l1_pre_topc @ sk_C_1)
% 0.51/0.68        | ~ (v2_pre_topc @ sk_C_1)
% 0.51/0.68        | ~ (m1_pre_topc @ sk_D @ sk_C_1)
% 0.51/0.68        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['54', '58'])).
% 0.51/0.68  thf('60', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('61', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('62', plain,
% 0.51/0.68      (![X7 : $i, X8 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X7 @ X8)
% 0.51/0.68          | (v2_pre_topc @ X7)
% 0.51/0.68          | ~ (l1_pre_topc @ X8)
% 0.51/0.68          | ~ (v2_pre_topc @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.51/0.68  thf('63', plain,
% 0.51/0.68      ((~ (v2_pre_topc @ sk_A)
% 0.51/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.68        | (v2_pre_topc @ sk_C_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['61', '62'])).
% 0.51/0.68  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('66', plain, ((v2_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.51/0.68  thf('67', plain,
% 0.51/0.68      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.68      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.68  thf('68', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('69', plain,
% 0.51/0.68      (![X6 : $i]:
% 0.51/0.68         (~ (v1_pre_topc @ X6)
% 0.51/0.68          | ((X6) = (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.51/0.68          | ~ (l1_pre_topc @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.51/0.68  thf('70', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X2)
% 0.51/0.68          | (m1_pre_topc @ X1 @ X2)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.51/0.68              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.51/0.68          | ~ (l1_pre_topc @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0))),
% 0.51/0.68      inference('simplify', [status(thm)], ['30'])).
% 0.51/0.68  thf('71', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v1_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X2)
% 0.51/0.68          | ~ (m1_pre_topc @ X2 @ X0)
% 0.51/0.68          | (m1_pre_topc @ X2 @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.51/0.68  thf('72', plain,
% 0.51/0.68      (![X1 : $i, X2 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X1)
% 0.51/0.68          | (m1_pre_topc @ X2 @ X1)
% 0.51/0.68          | ~ (m1_pre_topc @ X2 @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.51/0.68          | ~ (l1_pre_topc @ X2)
% 0.51/0.68          | ~ (v1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.51/0.68          | ~ (l1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.51/0.68  thf('73', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (v1_pre_topc @ sk_D)
% 0.51/0.68          | ~ (l1_pre_topc @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X0 @ 
% 0.51/0.68               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.51/0.68          | (m1_pre_topc @ X0 @ sk_C_1)
% 0.51/0.68          | ~ (l1_pre_topc @ sk_C_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['68', '72'])).
% 0.51/0.68  thf('74', plain, ((v1_pre_topc @ sk_D)),
% 0.51/0.68      inference('clc', [status(thm)], ['43', '44'])).
% 0.51/0.68  thf('75', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('77', plain,
% 0.51/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.51/0.68         = (sk_D))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('78', plain, ((l1_pre_topc @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.68  thf('79', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.51/0.68          | (m1_pre_topc @ X0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['73', '74', '75', '76', '77', '78'])).
% 0.51/0.68  thf('80', plain,
% 0.51/0.68      ((~ (l1_pre_topc @ sk_D)
% 0.51/0.68        | (m1_pre_topc @ sk_D @ sk_C_1)
% 0.51/0.68        | ~ (l1_pre_topc @ sk_D))),
% 0.51/0.68      inference('sup-', [status(thm)], ['67', '79'])).
% 0.51/0.68  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('83', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.51/0.68  thf('84', plain,
% 0.51/0.68      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.51/0.68      inference('demod', [status(thm)], ['59', '60', '66', '83'])).
% 0.51/0.68  thf(d10_xboole_0, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.68  thf('85', plain,
% 0.51/0.68      (![X0 : $i, X2 : $i]:
% 0.51/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.51/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.68  thf('86', plain,
% 0.51/0.68      ((~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.51/0.68  thf('87', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.51/0.68      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.51/0.68  thf('88', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.68          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | ~ (l1_pre_topc @ X0))),
% 0.51/0.68      inference('simplify', [status(thm)], ['57'])).
% 0.51/0.68  thf('89', plain,
% 0.51/0.68      ((~ (l1_pre_topc @ sk_D)
% 0.51/0.68        | ~ (v2_pre_topc @ sk_D)
% 0.51/0.68        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.51/0.68        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.68  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('91', plain, ((v2_pre_topc @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.51/0.68  thf('92', plain,
% 0.51/0.68      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.51/0.68        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.51/0.68      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.51/0.68  thf('93', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.51/0.68  thf('94', plain,
% 0.51/0.68      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['92', '93'])).
% 0.51/0.68  thf('95', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['86', '94'])).
% 0.51/0.68  thf('96', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.51/0.68          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.51/0.68      inference('demod', [status(thm)], ['25', '95'])).
% 0.51/0.68  thf('97', plain,
% 0.51/0.68      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.51/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['17', '96'])).
% 0.51/0.68  thf('98', plain,
% 0.51/0.68      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.51/0.68        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('99', plain, (((sk_F) = (sk_G))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('100', plain,
% 0.51/0.68      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.51/0.68        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.51/0.68      inference('demod', [status(thm)], ['98', '99'])).
% 0.51/0.68  thf('101', plain,
% 0.51/0.68      ((m1_subset_1 @ sk_E @ 
% 0.51/0.68        (k1_zfmisc_1 @ 
% 0.51/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(t83_tmap_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.68             ( l1_pre_topc @ B ) ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.68               ( ![D:$i]:
% 0.51/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.68                   ( ![E:$i]:
% 0.51/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.68                         ( v1_funct_2 @
% 0.51/0.68                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.68                         ( m1_subset_1 @
% 0.51/0.68                           E @ 
% 0.51/0.68                           ( k1_zfmisc_1 @
% 0.51/0.68                             ( k2_zfmisc_1 @
% 0.51/0.68                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.68                       ( ( m1_pre_topc @ C @ D ) =>
% 0.51/0.68                         ( ![F:$i]:
% 0.51/0.68                           ( ( m1_subset_1 @
% 0.51/0.68                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.51/0.68                             ( ![G:$i]:
% 0.51/0.68                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.68                                 ( ![H:$i]:
% 0.51/0.68                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.68                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.51/0.68                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.51/0.68                                         ( ( G ) = ( H ) ) ) =>
% 0.51/0.68                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.51/0.68                                         ( r1_tmap_1 @
% 0.51/0.68                                           C @ B @ 
% 0.51/0.68                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.51/0.68                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.68  thf('102', plain,
% 0.51/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.51/0.68         X35 : $i]:
% 0.51/0.68         ((v2_struct_0 @ X28)
% 0.51/0.68          | ~ (v2_pre_topc @ X28)
% 0.51/0.68          | ~ (l1_pre_topc @ X28)
% 0.51/0.68          | (v2_struct_0 @ X29)
% 0.51/0.68          | ~ (m1_pre_topc @ X29 @ X30)
% 0.51/0.68          | ~ (m1_pre_topc @ X31 @ X29)
% 0.51/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.51/0.68          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.51/0.68          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.51/0.68               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.51/0.68          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X35)
% 0.51/0.68          | ((X35) != (X33))
% 0.51/0.68          | ~ (m1_connsp_2 @ X32 @ X29 @ X35)
% 0.51/0.68          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X31))
% 0.51/0.68          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X29))
% 0.51/0.68          | ~ (m1_subset_1 @ X34 @ 
% 0.51/0.68               (k1_zfmisc_1 @ 
% 0.51/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.51/0.68          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.51/0.68          | ~ (v1_funct_1 @ X34)
% 0.51/0.68          | ~ (m1_pre_topc @ X31 @ X30)
% 0.51/0.68          | (v2_struct_0 @ X31)
% 0.51/0.68          | ~ (l1_pre_topc @ X30)
% 0.51/0.68          | ~ (v2_pre_topc @ X30)
% 0.51/0.68          | (v2_struct_0 @ X30))),
% 0.51/0.68      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.51/0.68  thf('103', plain,
% 0.51/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.68         ((v2_struct_0 @ X30)
% 0.51/0.68          | ~ (v2_pre_topc @ X30)
% 0.51/0.68          | ~ (l1_pre_topc @ X30)
% 0.51/0.68          | (v2_struct_0 @ X31)
% 0.51/0.68          | ~ (m1_pre_topc @ X31 @ X30)
% 0.51/0.68          | ~ (v1_funct_1 @ X34)
% 0.51/0.68          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.51/0.68          | ~ (m1_subset_1 @ X34 @ 
% 0.51/0.68               (k1_zfmisc_1 @ 
% 0.51/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.51/0.68          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.51/0.68          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X31))
% 0.51/0.68          | ~ (m1_connsp_2 @ X32 @ X29 @ X33)
% 0.51/0.68          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 0.51/0.68          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.51/0.68               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.51/0.68          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.51/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.51/0.68          | ~ (m1_pre_topc @ X31 @ X29)
% 0.51/0.68          | ~ (m1_pre_topc @ X29 @ X30)
% 0.51/0.68          | (v2_struct_0 @ X29)
% 0.51/0.68          | ~ (l1_pre_topc @ X28)
% 0.51/0.68          | ~ (v2_pre_topc @ X28)
% 0.51/0.68          | (v2_struct_0 @ X28))),
% 0.51/0.68      inference('simplify', [status(thm)], ['102'])).
% 0.51/0.68  thf('104', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         ((v2_struct_0 @ sk_B)
% 0.51/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.51/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.51/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.51/0.68               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.51/0.68          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.51/0.68          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.51/0.68          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.51/0.68          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.68          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | (v2_struct_0 @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | (v2_struct_0 @ X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['101', '103'])).
% 0.51/0.68  thf('105', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('107', plain,
% 0.51/0.68      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('109', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         ((v2_struct_0 @ sk_B)
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.51/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.51/0.68               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.51/0.68          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.51/0.68          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.51/0.68          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | (v2_struct_0 @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | (v2_struct_0 @ X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.51/0.68  thf('110', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['86', '94'])).
% 0.51/0.68  thf('111', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['86', '94'])).
% 0.51/0.68  thf('112', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         ((v2_struct_0 @ sk_B)
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.51/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.51/0.68               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.51/0.68          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.51/0.68          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.51/0.68          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.68          | (v2_struct_0 @ X1)
% 0.51/0.68          | ~ (l1_pre_topc @ X0)
% 0.51/0.68          | ~ (v2_pre_topc @ X0)
% 0.51/0.68          | (v2_struct_0 @ X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.51/0.68  thf('113', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((v2_struct_0 @ sk_A)
% 0.51/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.68          | (v2_struct_0 @ sk_C_1)
% 0.51/0.68          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.51/0.68          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.51/0.68          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.68          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.51/0.68          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.51/0.68          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | (v2_struct_0 @ sk_B))),
% 0.51/0.68      inference('sup-', [status(thm)], ['100', '112'])).
% 0.51/0.68  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('116', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('117', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('118', plain, (((sk_F) = (sk_G))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('119', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.68  thf('120', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.68  thf('121', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.51/0.68      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.51/0.68  thf('122', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('123', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         ((v2_struct_0 @ sk_A)
% 0.51/0.68          | (v2_struct_0 @ sk_C_1)
% 0.51/0.68          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.51/0.68          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.51/0.68          | (v2_struct_0 @ sk_D)
% 0.51/0.68          | (v2_struct_0 @ sk_B))),
% 0.51/0.68      inference('demod', [status(thm)],
% 0.51/0.68                ['113', '114', '115', '116', '119', '120', '121', '122'])).
% 0.51/0.68  thf('124', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_B)
% 0.51/0.68        | (v2_struct_0 @ sk_D)
% 0.51/0.68        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.68        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.51/0.68        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.51/0.68        | (v2_struct_0 @ sk_C_1)
% 0.51/0.68        | (v2_struct_0 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['97', '123'])).
% 0.51/0.68  thf('125', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.51/0.68      inference('clc', [status(thm)], ['15', '16'])).
% 0.51/0.68  thf('126', plain,
% 0.51/0.68      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.51/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['17', '96'])).
% 0.51/0.68  thf(t3_subset, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.68  thf('127', plain,
% 0.51/0.68      (![X3 : $i, X4 : $i]:
% 0.51/0.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.68  thf('128', plain,
% 0.51/0.68      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['126', '127'])).
% 0.51/0.68  thf('129', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_B)
% 0.51/0.68        | (v2_struct_0 @ sk_D)
% 0.51/0.68        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.68        | (v2_struct_0 @ sk_C_1)
% 0.51/0.68        | (v2_struct_0 @ sk_A))),
% 0.51/0.68      inference('demod', [status(thm)], ['124', '125', '128'])).
% 0.51/0.68  thf('130', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('131', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_A)
% 0.51/0.68        | (v2_struct_0 @ sk_C_1)
% 0.51/0.68        | (v2_struct_0 @ sk_D)
% 0.51/0.68        | (v2_struct_0 @ sk_B))),
% 0.51/0.68      inference('sup-', [status(thm)], ['129', '130'])).
% 0.51/0.68  thf('132', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('133', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['131', '132'])).
% 0.51/0.68  thf('134', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('135', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.51/0.68      inference('clc', [status(thm)], ['133', '134'])).
% 0.51/0.68  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('137', plain, ((v2_struct_0 @ sk_C_1)),
% 0.51/0.68      inference('clc', [status(thm)], ['135', '136'])).
% 0.51/0.68  thf('138', plain, ($false), inference('demod', [status(thm)], ['0', '137'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
