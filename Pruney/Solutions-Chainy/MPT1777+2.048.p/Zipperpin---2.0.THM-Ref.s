%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vMWj45WOO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  160 (1558 expanded)
%              Number of leaves         :   36 ( 473 expanded)
%              Depth                    :   23
%              Number of atoms          : 1544 (47337 expanded)
%              Number of equality atoms :   26 (1250 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_C @ X17 @ X16 ) @ X16 @ X17 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32','33','38'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('47',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
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

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( X18
       != ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( m1_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) @ X20 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('52',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('54',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('56',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55','61'])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('65',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('66',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','70'])).

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
    inference(demod,[status(thm)],['45','70'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','70'])).

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

thf('81',plain,(
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
    inference(demod,[status(thm)],['45','70'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','70'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','70'])).

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
    inference(demod,[status(thm)],['45','70'])).

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
    inference(demod,[status(thm)],['63','64','65'])).

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
    inference(demod,[status(thm)],['45','70'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vMWj45WOO
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:47:19 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 149 iterations in 0.068s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(t88_tmap_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.54             ( l1_pre_topc @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.54                   ( ![E:$i]:
% 0.22/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.54                         ( v1_funct_2 @
% 0.22/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.54                         ( m1_subset_1 @
% 0.22/0.54                           E @ 
% 0.22/0.54                           ( k1_zfmisc_1 @
% 0.22/0.54                             ( k2_zfmisc_1 @
% 0.22/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.54                       ( ( ( g1_pre_topc @
% 0.22/0.54                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.54                           ( D ) ) =>
% 0.22/0.54                         ( ![F:$i]:
% 0.22/0.54                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.54                             ( ![G:$i]:
% 0.22/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.54                                 ( ( ( ( F ) = ( G ) ) & 
% 0.22/0.54                                     ( r1_tmap_1 @
% 0.22/0.54                                       C @ B @ 
% 0.22/0.54                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.22/0.54                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54            ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.54                ( l1_pre_topc @ B ) ) =>
% 0.22/0.54              ( ![C:$i]:
% 0.22/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.54                  ( ![D:$i]:
% 0.22/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.54                      ( ![E:$i]:
% 0.22/0.54                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.54                            ( v1_funct_2 @
% 0.22/0.54                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.54                            ( m1_subset_1 @
% 0.22/0.54                              E @ 
% 0.22/0.54                              ( k1_zfmisc_1 @
% 0.22/0.54                                ( k2_zfmisc_1 @
% 0.22/0.54                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.54                          ( ( ( g1_pre_topc @
% 0.22/0.54                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.54                              ( D ) ) =>
% 0.22/0.54                            ( ![F:$i]:
% 0.22/0.54                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.54                                ( ![G:$i]:
% 0.22/0.54                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.54                                    ( ( ( ( F ) = ( G ) ) & 
% 0.22/0.54                                        ( r1_tmap_1 @
% 0.22/0.54                                          C @ B @ 
% 0.22/0.54                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.22/0.54                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.22/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(existence_m1_connsp_2, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X16)
% 0.22/0.54          | ~ (v2_pre_topc @ X16)
% 0.22/0.54          | (v2_struct_0 @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.54          | (m1_connsp_2 @ (sk_C @ X17 @ X16) @ X16 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_D)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.22/0.54          | (v2_pre_topc @ X6)
% 0.22/0.54          | ~ (l1_pre_topc @ X7)
% 0.22/0.54          | ~ (v2_pre_topc @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('9', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.54  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_m1_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.54  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '9', '14'])).
% 0.22/0.54  thf('16', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('17', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.22/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_m1_connsp_2, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54       ( ![C:$i]:
% 0.22/0.54         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.22/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X13)
% 0.22/0.54          | ~ (v2_pre_topc @ X13)
% 0.22/0.54          | (v2_struct_0 @ X13)
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.22/0.54          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.54          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.22/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.54  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.22/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.54          | (v2_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.54  thf('24', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.54          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F))),
% 0.22/0.54      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.22/0.54         = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t2_tsep_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.54  thf(t59_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_pre_topc @
% 0.22/0.54             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.54           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X11 @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.22/0.54          | (m1_pre_topc @ X11 @ X12)
% 0.22/0.54          | ~ (l1_pre_topc @ X12))),
% 0.22/0.54      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (m1_pre_topc @ 
% 0.22/0.54             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.54        | (m1_pre_topc @ 
% 0.22/0.54           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 0.22/0.54           sk_C_1)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.54  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.22/0.54         = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('34', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.54  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('38', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '32', '33', '38'])).
% 0.22/0.54  thf(t35_borsuk_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.54           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X22 : $i, X23 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X22 @ X23)
% 0.22/0.54          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.22/0.54          | ~ (l1_pre_topc @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.54        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.22/0.54        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.22/0.54         = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t12_tmap_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.22/0.54               ( ( ( B ) =
% 0.22/0.54                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.22/0.54                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (v2_pre_topc @ X18)
% 0.22/0.54          | ~ (l1_pre_topc @ X18)
% 0.22/0.54          | ((X18) != (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.22/0.54          | ~ (m1_pre_topc @ X18 @ X20)
% 0.22/0.54          | (m1_pre_topc @ X19 @ X20)
% 0.22/0.54          | ~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (v2_pre_topc @ X19)
% 0.22/0.54          | ~ (l1_pre_topc @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X20)
% 0.22/0.54          | ~ (v2_pre_topc @ X19)
% 0.22/0.54          | ~ (l1_pre_topc @ X19)
% 0.22/0.54          | (m1_pre_topc @ X19 @ X20)
% 0.22/0.54          | ~ (m1_pre_topc @ 
% 0.22/0.54               (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)) @ X20)
% 0.22/0.54          | ~ (l1_pre_topc @ 
% 0.22/0.54               (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.22/0.54          | ~ (v2_pre_topc @ 
% 0.22/0.54               (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_D)
% 0.22/0.54          | ~ (v2_pre_topc @ 
% 0.22/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.22/0.54          | ~ (m1_pre_topc @ 
% 0.22/0.54               (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 0.22/0.54               X0)
% 0.22/0.54          | (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_C_1)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_C_1)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['47', '49'])).
% 0.22/0.54  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.22/0.54         = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('53', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.22/0.54         = (sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('55', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('56', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.22/0.54          | (v2_pre_topc @ X6)
% 0.22/0.54          | ~ (l1_pre_topc @ X7)
% 0.22/0.54          | ~ (v2_pre_topc @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_pre_topc @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.54  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain, ((v2_pre_topc @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('demod', [status(thm)],
% 0.22/0.54                ['50', '51', '52', '53', '54', '55', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_D)
% 0.22/0.54        | (m1_pre_topc @ sk_C_1 @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['46', '62'])).
% 0.22/0.54  thf('64', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('65', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('66', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      (![X22 : $i, X23 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X22 @ X23)
% 0.22/0.54          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.22/0.54          | ~ (l1_pre_topc @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.54        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.54  thf('69', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.54  thf('71', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '71'])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.22/0.54        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('74', plain, (((sk_F) = (sk_G))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('75', plain,
% 0.22/0.54      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.22/0.54        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.22/0.54      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.54  thf('76', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_E @ 
% 0.22/0.54        (k1_zfmisc_1 @ 
% 0.22/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('77', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('78', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_E @ 
% 0.22/0.54        (k1_zfmisc_1 @ 
% 0.22/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.54      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.54  thf('79', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf(t83_tmap_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.54             ( l1_pre_topc @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.54                   ( ![E:$i]:
% 0.22/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.54                         ( v1_funct_2 @
% 0.22/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.54                         ( m1_subset_1 @
% 0.22/0.54                           E @ 
% 0.22/0.54                           ( k1_zfmisc_1 @
% 0.22/0.54                             ( k2_zfmisc_1 @
% 0.22/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.54                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.54                         ( ![F:$i]:
% 0.22/0.54                           ( ( m1_subset_1 @
% 0.22/0.54                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.22/0.54                             ( ![G:$i]:
% 0.22/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.54                                 ( ![H:$i]:
% 0.22/0.54                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.54                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.54                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.22/0.54                                         ( ( G ) = ( H ) ) ) =>
% 0.22/0.54                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.22/0.54                                         ( r1_tmap_1 @
% 0.22/0.54                                           C @ B @ 
% 0.22/0.54                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.22/0.54                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('80', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 0.22/0.54         X34 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X27)
% 0.22/0.54          | ~ (v2_pre_topc @ X27)
% 0.22/0.54          | ~ (l1_pre_topc @ X27)
% 0.22/0.54          | (v2_struct_0 @ X28)
% 0.22/0.54          | ~ (m1_pre_topc @ X28 @ X29)
% 0.22/0.54          | ~ (m1_pre_topc @ X30 @ X28)
% 0.22/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.22/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.22/0.54          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.22/0.54               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.22/0.54          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X34)
% 0.22/0.54          | ((X34) != (X32))
% 0.22/0.54          | ~ (m1_connsp_2 @ X31 @ X28 @ X34)
% 0.22/0.54          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.54          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X28))
% 0.22/0.54          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.54               (k1_zfmisc_1 @ 
% 0.22/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.22/0.54          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.22/0.54          | ~ (v1_funct_1 @ X33)
% 0.22/0.54          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.54          | (v2_struct_0 @ X30)
% 0.22/0.54          | ~ (l1_pre_topc @ X29)
% 0.22/0.54          | ~ (v2_pre_topc @ X29)
% 0.22/0.54          | (v2_struct_0 @ X29))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X29)
% 0.22/0.54          | ~ (v2_pre_topc @ X29)
% 0.22/0.54          | ~ (l1_pre_topc @ X29)
% 0.22/0.54          | (v2_struct_0 @ X30)
% 0.22/0.54          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.54          | ~ (v1_funct_1 @ X33)
% 0.22/0.54          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.22/0.54          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.54               (k1_zfmisc_1 @ 
% 0.22/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.22/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.22/0.54          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.54          | ~ (m1_connsp_2 @ X31 @ X28 @ X32)
% 0.22/0.54          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.22/0.54          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.22/0.54               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.22/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.22/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.22/0.54          | ~ (m1_pre_topc @ X30 @ X28)
% 0.22/0.54          | ~ (m1_pre_topc @ X28 @ X29)
% 0.22/0.54          | (v2_struct_0 @ X28)
% 0.22/0.54          | ~ (l1_pre_topc @ X27)
% 0.22/0.54          | ~ (v2_pre_topc @ X27)
% 0.22/0.54          | (v2_struct_0 @ X27))),
% 0.22/0.54      inference('simplify', [status(thm)], ['80'])).
% 0.22/0.54  thf('82', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.54             (k1_zfmisc_1 @ 
% 0.22/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.22/0.54          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.22/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.22/0.54          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.22/0.54               X5)
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.22/0.54          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.22/0.54          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.22/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.22/0.54          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (v1_funct_1 @ X1)
% 0.22/0.54          | ~ (m1_pre_topc @ X3 @ X2)
% 0.22/0.54          | (v2_struct_0 @ X3)
% 0.22/0.54          | ~ (l1_pre_topc @ X2)
% 0.22/0.54          | ~ (v2_pre_topc @ X2)
% 0.22/0.54          | (v2_struct_0 @ X2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['79', '81'])).
% 0.22/0.54  thf('83', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('84', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('85', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('86', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.54             (k1_zfmisc_1 @ 
% 0.22/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.22/0.54          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.22/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.22/0.54          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.22/0.54               X5)
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.22/0.54          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.22/0.54          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.22/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (v1_funct_1 @ X1)
% 0.22/0.54          | ~ (m1_pre_topc @ X3 @ X2)
% 0.22/0.54          | (v2_struct_0 @ X3)
% 0.22/0.54          | ~ (l1_pre_topc @ X2)
% 0.22/0.54          | ~ (v2_pre_topc @ X2)
% 0.22/0.54          | (v2_struct_0 @ X2))),
% 0.22/0.54      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.22/0.54  thf('87', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.54               (u1_struct_0 @ sk_B))
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.54          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.54          | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['78', '86'])).
% 0.22/0.54  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('89', plain,
% 0.22/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('90', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('91', plain,
% 0.22/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.54  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('94', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.54          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['87', '88', '91', '92', '93'])).
% 0.22/0.54  thf('95', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.54          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_C_1)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['75', '94'])).
% 0.22/0.54  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('97', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.22/0.54  thf('98', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('99', plain, (((sk_F) = (sk_G))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('100', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.54  thf('101', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.54  thf('102', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('105', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_B)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.54          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54          | (v2_struct_0 @ sk_C_1)
% 0.22/0.54          | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)],
% 0.22/0.54                ['95', '96', '97', '100', '101', '102', '103', '104'])).
% 0.22/0.54  thf('106', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | ~ (r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54        | ~ (m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)
% 0.22/0.54        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['72', '105'])).
% 0.22/0.54  thf('107', plain,
% 0.22/0.54      ((m1_subset_1 @ (sk_C @ sk_F @ sk_D) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '25'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('108', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('109', plain,
% 0.22/0.54      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.54  thf('110', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '70'])).
% 0.22/0.54  thf('111', plain,
% 0.22/0.54      ((r1_tarski @ (sk_C @ sk_F @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['109', '110'])).
% 0.22/0.54  thf('112', plain, ((m1_connsp_2 @ (sk_C @ sk_F @ sk_D) @ sk_D @ sk_F)),
% 0.22/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('113', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['106', '111', '112'])).
% 0.22/0.54  thf('114', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('115', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.22/0.54  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('117', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['115', '116'])).
% 0.22/0.54  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('119', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('clc', [status(thm)], ['117', '118'])).
% 0.22/0.54  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('121', plain, ((v2_struct_0 @ sk_C_1)),
% 0.22/0.54      inference('clc', [status(thm)], ['119', '120'])).
% 0.22/0.54  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
