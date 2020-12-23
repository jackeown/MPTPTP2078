%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNRYUgErgp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 743 expanded)
%              Number of leaves         :   39 ( 232 expanded)
%              Depth                    :   20
%              Number of atoms          : 1627 (23465 expanded)
%              Number of equality atoms :   39 ( 712 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_connsp_2 @ ( sk_C @ X18 @ X17 ) @ X17 @ X18 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_connsp_2 @ X16 @ X14 @ X15 ) ) ),
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

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('25',plain,(
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

thf('26',plain,(
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

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_pre_topc @ X12 @ X13 )
       != ( g1_pre_topc @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X9: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('34',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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

thf('40',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','49'])).

thf('51',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

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

thf('58',plain,(
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

thf('59',plain,(
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
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('64',plain,(
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
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','42','43','44','45'])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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
    inference(demod,[status(thm)],['65','66','69','70','71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['53','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_pre_topc @ X19 @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('84',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k1_tsep_1 @ X23 @ X22 @ X22 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1 )
      = sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1 )
      = sk_D ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1 )
    = sk_D ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('104',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','99','102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','107'])).

thf('109',plain,(
    m1_subset_1 @ ( sk_C @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    r1_tarski @ ( sk_C @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_connsp_2 @ ( sk_C @ sk_F @ sk_D ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['15','16'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','111','112'])).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNRYUgErgp
% 0.13/0.36  % Computer   : n023.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 149 iterations in 0.099s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(t88_tmap_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.55             ( l1_pre_topc @ B ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.55               ( ![D:$i]:
% 0.21/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.55                   ( ![E:$i]:
% 0.21/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.55                         ( v1_funct_2 @
% 0.21/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.55                         ( m1_subset_1 @
% 0.21/0.55                           E @ 
% 0.21/0.55                           ( k1_zfmisc_1 @
% 0.21/0.55                             ( k2_zfmisc_1 @
% 0.21/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.55                       ( ( ( g1_pre_topc @
% 0.21/0.55                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.55                           ( D ) ) =>
% 0.21/0.55                         ( ![F:$i]:
% 0.21/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.55                             ( ![G:$i]:
% 0.21/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.55                                 ( ( ( ( F ) = ( G ) ) & 
% 0.21/0.55                                     ( r1_tmap_1 @
% 0.21/0.55                                       C @ B @ 
% 0.21/0.55                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.21/0.55                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.55                ( l1_pre_topc @ B ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.55                  ( ![D:$i]:
% 0.21/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.55                      ( ![E:$i]:
% 0.21/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.55                            ( v1_funct_2 @
% 0.21/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.55                            ( m1_subset_1 @
% 0.21/0.55                              E @ 
% 0.21/0.55                              ( k1_zfmisc_1 @
% 0.21/0.55                                ( k2_zfmisc_1 @
% 0.21/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.55                          ( ( ( g1_pre_topc @
% 0.21/0.55                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.55                              ( D ) ) =>
% 0.21/0.55                            ( ![F:$i]:
% 0.21/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.55                                ( ![G:$i]:
% 0.21/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.55                                    ( ( ( ( F ) = ( G ) ) & 
% 0.21/0.55                                        ( r1_tmap_1 @
% 0.21/0.55                                          C @ B @ 
% 0.21/0.55                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.21/0.55                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.21/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(existence_m1_connsp_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X17)
% 0.21/0.55          | ~ (v2_pre_topc @ X17)
% 0.21/0.55          | (v2_struct_0 @ X17)
% 0.21/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.21/0.55          | (m1_connsp_2 @ (sk_C @ X18 @ X17) @ X17 @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.21/0.55        | (v2_struct_0 @ sk_D)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_D)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.55          | (v2_pre_topc @ X4)
% 0.21/0.55          | ~ (l1_pre_topc @ X5)
% 0.21/0.55          | ~ (v2_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.55  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_m1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.55  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.21/0.55        | (v2_struct_0 @ sk_D))),
% 0.21/0.55      inference('demod', [status(thm)], ['3', '9', '14'])).
% 0.21/0.55  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_m1_connsp_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.21/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X14)
% 0.21/0.55          | ~ (v2_pre_topc @ X14)
% 0.21/0.55          | (v2_struct_0 @ X14)
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.21/0.55          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | ~ (m1_connsp_2 @ X16 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.55  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.55          | (v2_struct_0 @ sk_D))),
% 0.21/0.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.21/0.55         = (sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ( v1_pre_topc @ A ) =>
% 0.21/0.55         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X3 : $i]:
% 0.21/0.55         (~ (v1_pre_topc @ X3)
% 0.21/0.55          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.21/0.55          | ~ (l1_pre_topc @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.55  thf(dt_u1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( m1_subset_1 @
% 0.21/0.55         ( u1_pre_topc @ A ) @ 
% 0.21/0.55         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X8 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.55          | ~ (l1_pre_topc @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.55  thf(free_g1_pre_topc, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ![C:$i,D:$i]:
% 0.21/0.55         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.55           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         (((g1_pre_topc @ X12 @ X13) != (g1_pre_topc @ X10 @ X11))
% 0.21/0.55          | ((X12) = (X10))
% 0.21/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.21/0.55      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.21/0.55          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.55              != (g1_pre_topc @ X1 @ X2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_pre_topc @ X0)
% 0.21/0.55          | ((u1_struct_0 @ X0) = (X2))
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i]:
% 0.21/0.55         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.21/0.55          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.21/0.55          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((~ (v1_pre_topc @ sk_D)
% 0.21/0.55        | ~ (l1_pre_topc @ 
% 0.21/0.55             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.21/0.55        | ((u1_struct_0 @ 
% 0.21/0.55            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.21/0.55            = (u1_struct_0 @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.21/0.55         = (sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(fc7_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @
% 0.21/0.55              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.21/0.55         ( v1_pre_topc @
% 0.21/0.55           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         ((v1_pre_topc @ 
% 0.21/0.55           (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.21/0.55          | ~ (l1_pre_topc @ X9)
% 0.21/0.55          | (v2_struct_0 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((v1_pre_topc @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.55  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '39'])).
% 0.21/0.55  thf('41', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain, ((v1_pre_topc @ sk_D)),
% 0.21/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.21/0.55         = (sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('44', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.21/0.55         = (sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | (v2_struct_0 @ sk_D))),
% 0.21/0.55      inference('demod', [status(thm)], ['23', '46'])).
% 0.21/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.21/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('52', plain, (((sk_F) = (sk_G))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf(t83_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.55             ( l1_pre_topc @ B ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.55               ( ![D:$i]:
% 0.21/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.55                   ( ![E:$i]:
% 0.21/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.55                         ( v1_funct_2 @
% 0.21/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.55                         ( m1_subset_1 @
% 0.21/0.55                           E @ 
% 0.21/0.55                           ( k1_zfmisc_1 @
% 0.21/0.55                             ( k2_zfmisc_1 @
% 0.21/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.55                         ( ![F:$i]:
% 0.21/0.55                           ( ( m1_subset_1 @
% 0.21/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.55                             ( ![G:$i]:
% 0.21/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.55                                 ( ![H:$i]:
% 0.21/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.55                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.55                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.21/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.55                                         ( r1_tmap_1 @
% 0.21/0.55                                           C @ B @ 
% 0.21/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 0.21/0.55         X34 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X27)
% 0.21/0.55          | ~ (v2_pre_topc @ X27)
% 0.21/0.55          | ~ (l1_pre_topc @ X27)
% 0.21/0.55          | (v2_struct_0 @ X28)
% 0.21/0.55          | ~ (m1_pre_topc @ X28 @ X29)
% 0.21/0.55          | ~ (m1_pre_topc @ X30 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.21/0.55          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.21/0.55               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.21/0.55          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X34)
% 0.21/0.55          | ((X34) != (X32))
% 0.21/0.55          | ~ (m1_connsp_2 @ X31 @ X28 @ X34)
% 0.21/0.55          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.21/0.55          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X28))
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.21/0.55          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.21/0.55          | ~ (v1_funct_1 @ X33)
% 0.21/0.55          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.55          | (v2_struct_0 @ X30)
% 0.21/0.55          | ~ (l1_pre_topc @ X29)
% 0.21/0.55          | ~ (v2_pre_topc @ X29)
% 0.21/0.55          | (v2_struct_0 @ X29))),
% 0.21/0.55      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X29)
% 0.21/0.55          | ~ (v2_pre_topc @ X29)
% 0.21/0.55          | ~ (l1_pre_topc @ X29)
% 0.21/0.55          | (v2_struct_0 @ X30)
% 0.21/0.55          | ~ (m1_pre_topc @ X30 @ X29)
% 0.21/0.55          | ~ (v1_funct_1 @ X33)
% 0.21/0.55          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.21/0.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.21/0.55          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.21/0.55          | ~ (m1_connsp_2 @ X31 @ X28 @ X32)
% 0.21/0.55          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.21/0.55          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.21/0.55               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.21/0.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.55          | ~ (m1_pre_topc @ X30 @ X28)
% 0.21/0.55          | ~ (m1_pre_topc @ X28 @ X29)
% 0.21/0.55          | (v2_struct_0 @ X28)
% 0.21/0.55          | ~ (l1_pre_topc @ X27)
% 0.21/0.55          | ~ (v2_pre_topc @ X27)
% 0.21/0.55          | (v2_struct_0 @ X27))),
% 0.21/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.21/0.55          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.21/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.21/0.55          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.21/0.55               X5)
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.21/0.55          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.21/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (l1_pre_topc @ X2)
% 0.21/0.55          | ~ (v2_pre_topc @ X2)
% 0.21/0.55          | (v2_struct_0 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.55  thf('61', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('62', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('63', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.21/0.55          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.21/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.21/0.55          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.21/0.55               X5)
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.21/0.55          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (l1_pre_topc @ X2)
% 0.21/0.55          | ~ (v2_pre_topc @ X2)
% 0.21/0.55          | (v2_struct_0 @ X2))),
% 0.21/0.55      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X1)
% 0.21/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.21/0.55               (u1_struct_0 @ sk_B))
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.21/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.55          | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['56', '64'])).
% 0.21/0.55  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('68', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '42', '43', '44', '45'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X1)
% 0.21/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.21/0.55          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.55               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['65', '66', '69', '70', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_B)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.55          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.21/0.55          | (v2_struct_0 @ sk_C_1)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '72'])).
% 0.21/0.55  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('75', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('76', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t22_tsep_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.55               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X19)
% 0.21/0.55          | ~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.55          | (m1_pre_topc @ X19 @ (k1_tsep_1 @ X20 @ X19 @ X21))
% 0.21/0.55          | ~ (m1_pre_topc @ X21 @ X20)
% 0.21/0.55          | (v2_struct_0 @ X21)
% 0.21/0.55          | ~ (l1_pre_topc @ X20)
% 0.21/0.55          | ~ (v2_pre_topc @ X20)
% 0.21/0.55          | (v2_struct_0 @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.55          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_C_1 @ X0))
% 0.21/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.55  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.55          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_C_1 @ X0))
% 0.21/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1))
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '81'])).
% 0.21/0.55  thf('83', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t25_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.21/0.55             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X22)
% 0.21/0.55          | ~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.55          | ((k1_tsep_1 @ X23 @ X22 @ X22)
% 0.21/0.55              = (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.21/0.55          | ~ (l1_pre_topc @ X23)
% 0.21/0.55          | ~ (v2_pre_topc @ X23)
% 0.21/0.55          | (v2_struct_0 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1)
% 0.21/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.21/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.55  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.21/0.55         = (sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1) = (sk_D))
% 0.21/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.21/0.55  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_C_1)
% 0.21/0.55        | ((k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1) = (sk_D)))),
% 0.21/0.55      inference('clc', [status(thm)], ['89', '90'])).
% 0.21/0.55  thf('92', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('93', plain, (((k1_tsep_1 @ sk_A @ sk_C_1 @ sk_C_1) = (sk_D))),
% 0.21/0.55      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['82', '93'])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['94'])).
% 0.21/0.55  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('97', plain, (((v2_struct_0 @ sk_C_1) | (m1_pre_topc @ sk_C_1 @ sk_D))),
% 0.21/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('98', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('99', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.21/0.55      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.55  thf('100', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('101', plain, (((sk_F) = (sk_G))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('102', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('103', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('104', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('107', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_B)
% 0.21/0.55          | (v2_struct_0 @ sk_D)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.55          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.55          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55          | (v2_struct_0 @ sk_C_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)],
% 0.21/0.55                ['73', '74', '99', '102', '103', '104', '105', '106'])).
% 0.21/0.55  thf('108', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.55        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.21/0.55        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.55        | (v2_struct_0 @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['50', '107'])).
% 0.21/0.55  thf('109', plain,
% 0.21/0.55      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '49'])).
% 0.21/0.55  thf(t3_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('110', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.55  thf('111', plain,
% 0.21/0.55      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.55  thf('112', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('113', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.55        | (v2_struct_0 @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['108', '111', '112'])).
% 0.21/0.55  thf('114', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('115', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_B)
% 0.21/0.55        | (v2_struct_0 @ sk_D)
% 0.21/0.55        | (v2_struct_0 @ sk_C_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.55  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('117', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.55  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('119', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('clc', [status(thm)], ['117', '118'])).
% 0.21/0.55  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('121', plain, ((v2_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.55  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
