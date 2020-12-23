%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Upy4U5XlOZ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:36 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 423 expanded)
%              Number of leaves         :   41 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          : 1744 (13330 expanded)
%              Number of equality atoms :   36 ( 350 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','39','44','45','46','47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['3','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_tsep_1 @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ( r1_tmap_1 @ X29 @ X32 @ X33 @ X34 )
      | ( X34 != X31 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('64',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X32 @ X33 @ X31 )
      | ~ ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_tsep_1 @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('67',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['24','29'])).

thf('79',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('80',plain,(
    ! [X10: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

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

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('96',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_tsep_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( X21
       != ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( v1_tsep_1 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v1_tsep_1 @ X20 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t14_tmap_1])).

thf('98',plain,(
    ! [X20: $i,X22: $i] :
      ( ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ( v1_tsep_1 @ X20 @ X22 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) @ X22 )
      | ~ ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( v1_tsep_1 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('103',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('108',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tsep_1 @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','106','107','108','109','110','111'])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['95','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('115',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('116',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('117',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['94','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('120',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('121',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('122',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('123',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['118','119','120','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['73','74','77','78','124'])).

thf('126',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Upy4U5XlOZ
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 347 iterations in 0.143s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.59  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.39/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.39/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.39/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.39/0.59  thf(t88_tmap_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                         ( v1_funct_2 @
% 0.39/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                         ( m1_subset_1 @
% 0.39/0.59                           E @ 
% 0.39/0.59                           ( k1_zfmisc_1 @
% 0.39/0.59                             ( k2_zfmisc_1 @
% 0.39/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                       ( ( ( g1_pre_topc @
% 0.39/0.59                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.39/0.59                           ( D ) ) =>
% 0.39/0.59                         ( ![F:$i]:
% 0.39/0.59                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                             ( ![G:$i]:
% 0.39/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                                 ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.59                                     ( r1_tmap_1 @
% 0.39/0.59                                       C @ B @ 
% 0.39/0.59                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.39/0.59                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.59            ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59                ( l1_pre_topc @ B ) ) =>
% 0.39/0.59              ( ![C:$i]:
% 0.39/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.59                  ( ![D:$i]:
% 0.39/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.59                      ( ![E:$i]:
% 0.39/0.59                        ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                            ( v1_funct_2 @
% 0.39/0.59                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                            ( m1_subset_1 @
% 0.39/0.59                              E @ 
% 0.39/0.59                              ( k1_zfmisc_1 @
% 0.39/0.59                                ( k2_zfmisc_1 @
% 0.39/0.59                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                          ( ( ( g1_pre_topc @
% 0.39/0.59                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.39/0.59                              ( D ) ) =>
% 0.39/0.59                            ( ![F:$i]:
% 0.39/0.59                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                                ( ![G:$i]:
% 0.39/0.59                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                                    ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.59                                        ( r1_tmap_1 @
% 0.39/0.59                                          C @ B @ 
% 0.39/0.59                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.39/0.59                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.39/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.59        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('2', plain, (((sk_F) = (sk_G))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.59        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.39/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.39/0.59  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_E @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d5_tmap_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_pre_topc @ C @ A ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( m1_pre_topc @ D @ A ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.60                         ( v1_funct_2 @
% 0.39/0.60                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.60                         ( m1_subset_1 @
% 0.39/0.60                           E @ 
% 0.39/0.60                           ( k1_zfmisc_1 @
% 0.39/0.60                             ( k2_zfmisc_1 @
% 0.39/0.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.60                       ( ( m1_pre_topc @ D @ C ) =>
% 0.39/0.60                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.39/0.60                           ( k2_partfun1 @
% 0.39/0.60                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.39/0.60                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X15)
% 0.39/0.60          | ~ (v2_pre_topc @ X15)
% 0.39/0.60          | ~ (l1_pre_topc @ X15)
% 0.39/0.60          | ~ (m1_pre_topc @ X16 @ X17)
% 0.39/0.60          | ~ (m1_pre_topc @ X16 @ X18)
% 0.39/0.60          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.39/0.60                 X19 @ (u1_struct_0 @ X16)))
% 0.39/0.60          | ~ (m1_subset_1 @ X19 @ 
% 0.39/0.60               (k1_zfmisc_1 @ 
% 0.39/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.39/0.60          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.39/0.60          | ~ (v1_funct_1 @ X19)
% 0.39/0.60          | ~ (m1_pre_topc @ X18 @ X17)
% 0.39/0.60          | ~ (l1_pre_topc @ X17)
% 0.39/0.60          | ~ (v2_pre_topc @ X17)
% 0.39/0.60          | (v2_struct_0 @ X17))),
% 0.39/0.60      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X1)))
% 0.39/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.60  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X1)))
% 0.39/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_B)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.39/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.60          | (v2_struct_0 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['5', '13'])).
% 0.39/0.60  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_B)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.39/0.60          | (v2_struct_0 @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_A)
% 0.39/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.39/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60               sk_E @ (u1_struct_0 @ sk_C)))
% 0.39/0.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.39/0.60        | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '17'])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t2_tsep_1, axiom,
% 0.39/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.39/0.60  thf(t65_pre_topc, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_pre_topc @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( l1_pre_topc @ B ) =>
% 0.39/0.60           ( ( m1_pre_topc @ A @ B ) <=>
% 0.39/0.60             ( m1_pre_topc @
% 0.39/0.60               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X8 : $i, X9 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X8)
% 0.39/0.60          | ~ (m1_pre_topc @ X9 @ X8)
% 0.39/0.60          | (m1_pre_topc @ X9 @ 
% 0.39/0.60             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.39/0.60          | ~ (l1_pre_topc @ X9))),
% 0.39/0.60      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | (m1_pre_topc @ X0 @ 
% 0.39/0.60             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.60          | ~ (l1_pre_topc @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((m1_pre_topc @ X0 @ 
% 0.39/0.60           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.60          | ~ (l1_pre_topc @ X0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.60  thf('24', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.39/0.60      inference('sup+', [status(thm)], ['19', '23'])).
% 0.39/0.60  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(dt_m1_pre_topc, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_pre_topc @ A ) =>
% 0.39/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.60  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['24', '29'])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_E @ 
% 0.39/0.60        (k1_zfmisc_1 @ 
% 0.39/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(d4_tmap_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.60             ( l1_pre_topc @ B ) ) =>
% 0.39/0.60           ( ![C:$i]:
% 0.39/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.60                 ( m1_subset_1 @
% 0.39/0.60                   C @ 
% 0.39/0.60                   ( k1_zfmisc_1 @
% 0.39/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.60               ( ![D:$i]:
% 0.39/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.39/0.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.39/0.60                     ( k2_partfun1 @
% 0.39/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.39/0.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X11)
% 0.39/0.60          | ~ (v2_pre_topc @ X11)
% 0.39/0.60          | ~ (l1_pre_topc @ X11)
% 0.39/0.60          | ~ (m1_pre_topc @ X12 @ X13)
% 0.39/0.60          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.39/0.60                 X14 @ (u1_struct_0 @ X12)))
% 0.39/0.60          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.60               (k1_zfmisc_1 @ 
% 0.39/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.39/0.60          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.39/0.60          | ~ (v1_funct_1 @ X14)
% 0.39/0.60          | ~ (l1_pre_topc @ X13)
% 0.39/0.60          | ~ (v2_pre_topc @ X13)
% 0.39/0.60          | (v2_struct_0 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_D)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.39/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc1_pre_topc, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.60          | (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X1)
% 0.39/0.60          | ~ (v2_pre_topc @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.60  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('39', plain, ((v2_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.60  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('41', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.60  thf('42', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.60  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('44', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_D)
% 0.39/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.39/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)],
% 0.39/0.60                ['33', '39', '44', '45', '46', '47', '48'])).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_B)
% 0.39/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.39/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60               sk_E @ (u1_struct_0 @ sk_C)))
% 0.39/0.60        | (v2_struct_0 @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['30', '49'])).
% 0.39/0.60  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_D)
% 0.39/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.39/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.60               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.39/0.60      inference('clc', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf('53', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.39/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.39/0.60            (u1_struct_0 @ sk_C)))),
% 0.39/0.60      inference('clc', [status(thm)], ['52', '53'])).
% 0.39/0.60  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['24', '29'])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_A)
% 0.39/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.39/0.60            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.39/0.60        | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)], ['18', '54', '55'])).
% 0.39/0.60  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_B)
% 0.39/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.39/0.60            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.39/0.60      inference('clc', [status(thm)], ['56', '57'])).
% 0.39/0.60  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.39/0.60         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.39/0.60      inference('clc', [status(thm)], ['58', '59'])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.39/0.60        sk_F)),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '60'])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_E @ 
% 0.39/0.60        (k1_zfmisc_1 @ 
% 0.39/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t67_tmap_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.60             ( l1_pre_topc @ B ) ) =>
% 0.39/0.60           ( ![C:$i]:
% 0.39/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.60                 ( m1_subset_1 @
% 0.39/0.60                   C @ 
% 0.39/0.60                   ( k1_zfmisc_1 @
% 0.39/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.39/0.60               ( ![D:$i]:
% 0.39/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.39/0.60                     ( m1_pre_topc @ D @ B ) ) =>
% 0.39/0.60                   ( ![E:$i]:
% 0.39/0.60                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.39/0.60                       ( ![F:$i]:
% 0.39/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.60                           ( ( ( E ) = ( F ) ) =>
% 0.39/0.60                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.39/0.60                               ( r1_tmap_1 @
% 0.39/0.60                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X29)
% 0.39/0.60          | ~ (v2_pre_topc @ X29)
% 0.39/0.60          | ~ (l1_pre_topc @ X29)
% 0.39/0.60          | (v2_struct_0 @ X30)
% 0.39/0.60          | ~ (v1_tsep_1 @ X30 @ X29)
% 0.39/0.60          | ~ (m1_pre_topc @ X30 @ X29)
% 0.39/0.60          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.39/0.60          | ~ (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ 
% 0.39/0.60               X31)
% 0.39/0.60          | (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.39/0.60          | ((X34) != (X31))
% 0.39/0.60          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.39/0.60          | ~ (m1_subset_1 @ X33 @ 
% 0.39/0.60               (k1_zfmisc_1 @ 
% 0.39/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.39/0.60          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.39/0.60          | ~ (v1_funct_1 @ X33)
% 0.39/0.60          | ~ (l1_pre_topc @ X32)
% 0.39/0.60          | ~ (v2_pre_topc @ X32)
% 0.39/0.60          | (v2_struct_0 @ X32))),
% 0.39/0.60      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.60         ((v2_struct_0 @ X32)
% 0.39/0.60          | ~ (v2_pre_topc @ X32)
% 0.39/0.60          | ~ (l1_pre_topc @ X32)
% 0.39/0.60          | ~ (v1_funct_1 @ X33)
% 0.39/0.60          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.39/0.60          | ~ (m1_subset_1 @ X33 @ 
% 0.39/0.60               (k1_zfmisc_1 @ 
% 0.39/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.39/0.60          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.39/0.60          | (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.39/0.60          | ~ (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ 
% 0.39/0.60               X31)
% 0.39/0.60          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.39/0.60          | ~ (m1_pre_topc @ X30 @ X29)
% 0.39/0.60          | ~ (v1_tsep_1 @ X30 @ X29)
% 0.39/0.60          | (v2_struct_0 @ X30)
% 0.39/0.60          | ~ (l1_pre_topc @ X29)
% 0.39/0.60          | ~ (v2_pre_topc @ X29)
% 0.39/0.60          | (v2_struct_0 @ X29))),
% 0.39/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_D)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.39/0.60          | (v2_struct_0 @ X0)
% 0.39/0.60          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.39/0.60               X1)
% 0.39/0.60          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.39/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.39/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['62', '64'])).
% 0.39/0.60  thf('66', plain, ((v2_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.60  thf('67', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('68', plain,
% 0.39/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('72', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((v2_struct_0 @ sk_D)
% 0.39/0.60          | (v2_struct_0 @ X0)
% 0.39/0.60          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.39/0.60               X1)
% 0.39/0.60          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.39/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.39/0.60          | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)],
% 0.39/0.60                ['65', '66', '67', '68', '69', '70', '71'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_B)
% 0.39/0.60        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.39/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.39/0.60        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.39/0.60        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.39/0.60        | (v2_struct_0 @ sk_C)
% 0.39/0.60        | (v2_struct_0 @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['61', '72'])).
% 0.39/0.60  thf('74', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('75', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('76', plain, (((sk_F) = (sk_G))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('77', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.60  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['24', '29'])).
% 0.39/0.60  thf('79', plain,
% 0.39/0.60      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.39/0.60  thf(fc10_tops_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      (![X10 : $i]:
% 0.39/0.60         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.39/0.60          | ~ (l1_pre_topc @ X10)
% 0.39/0.60          | ~ (v2_pre_topc @ X10))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.39/0.60  thf(d3_struct_0, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.60  thf('81', plain,
% 0.39/0.60      (![X2 : $i]:
% 0.39/0.60         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.60  thf('82', plain,
% 0.39/0.60      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.39/0.60  thf(t1_tsep_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_pre_topc @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.60           ( m1_subset_1 @
% 0.39/0.60             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.60  thf('83', plain,
% 0.39/0.60      (![X26 : $i, X27 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X26 @ X27)
% 0.39/0.60          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.39/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.39/0.60          | ~ (l1_pre_topc @ X27))),
% 0.39/0.60      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.60  thf('84', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.60  thf('85', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.60          | ~ (l1_pre_topc @ X0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['84'])).
% 0.39/0.60  thf(t16_tsep_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.60           ( ![C:$i]:
% 0.39/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.60               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.60                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.60                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.60  thf('86', plain,
% 0.39/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X23 @ X24)
% 0.39/0.60          | ((X25) != (u1_struct_0 @ X23))
% 0.39/0.60          | ~ (v3_pre_topc @ X25 @ X24)
% 0.39/0.60          | (v1_tsep_1 @ X23 @ X24)
% 0.39/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.60          | ~ (l1_pre_topc @ X24)
% 0.39/0.60          | ~ (v2_pre_topc @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (![X23 : $i, X24 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ X24)
% 0.39/0.60          | ~ (l1_pre_topc @ X24)
% 0.39/0.60          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.39/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.60          | (v1_tsep_1 @ X23 @ X24)
% 0.39/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.39/0.60          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.39/0.60      inference('simplify', [status(thm)], ['86'])).
% 0.39/0.60  thf('88', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.39/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['85', '87'])).
% 0.39/0.60  thf('89', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.39/0.60  thf('90', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.39/0.60          | ~ (l1_struct_0 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['81', '89'])).
% 0.39/0.60  thf('91', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_struct_0 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['80', '90'])).
% 0.39/0.60  thf('92', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_struct_0 @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['91'])).
% 0.39/0.60  thf('93', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (l1_struct_0 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['79', '92'])).
% 0.39/0.60  thf('94', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (l1_struct_0 @ X0)
% 0.39/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['93'])).
% 0.39/0.60  thf('95', plain,
% 0.39/0.60      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.39/0.60  thf('96', plain,
% 0.39/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t14_tmap_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.60           ( ![C:$i]:
% 0.39/0.60             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.39/0.60               ( ( ( C ) =
% 0.39/0.60                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.39/0.60                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.60                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.60  thf('97', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ X20)
% 0.39/0.60          | ~ (l1_pre_topc @ X20)
% 0.39/0.60          | ((X21) != (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.39/0.60          | ~ (v1_tsep_1 @ X21 @ X22)
% 0.39/0.60          | ~ (m1_pre_topc @ X21 @ X22)
% 0.39/0.60          | (v1_tsep_1 @ X20 @ X22)
% 0.39/0.60          | ~ (l1_pre_topc @ X21)
% 0.39/0.60          | ~ (v2_pre_topc @ X21)
% 0.39/0.60          | ~ (l1_pre_topc @ X22)
% 0.39/0.60          | ~ (v2_pre_topc @ X22))),
% 0.39/0.60      inference('cnf', [status(esa)], [t14_tmap_1])).
% 0.39/0.60  thf('98', plain,
% 0.39/0.60      (![X20 : $i, X22 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ X22)
% 0.39/0.60          | ~ (l1_pre_topc @ X22)
% 0.39/0.60          | ~ (v2_pre_topc @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.39/0.60          | ~ (l1_pre_topc @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.39/0.60          | (v1_tsep_1 @ X20 @ X22)
% 0.39/0.60          | ~ (m1_pre_topc @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)) @ X22)
% 0.39/0.60          | ~ (v1_tsep_1 @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)) @ X22)
% 0.39/0.60          | ~ (l1_pre_topc @ X20)
% 0.39/0.60          | ~ (v2_pre_topc @ X20))),
% 0.39/0.60      inference('simplify', [status(thm)], ['97'])).
% 0.39/0.60  thf('99', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v2_pre_topc @ sk_D)
% 0.39/0.60          | ~ (v2_pre_topc @ sk_C)
% 0.39/0.60          | ~ (l1_pre_topc @ sk_C)
% 0.39/0.60          | ~ (v1_tsep_1 @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.39/0.60          | (v1_tsep_1 @ sk_C @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ 
% 0.39/0.60               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['96', '98'])).
% 0.39/0.60  thf('100', plain, ((v2_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.60  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('102', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.60          | (v2_pre_topc @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X1)
% 0.39/0.60          | ~ (v2_pre_topc @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.39/0.60  thf('103', plain,
% 0.39/0.60      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['101', '102'])).
% 0.39/0.60  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('106', plain, ((v2_pre_topc @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.39/0.60  thf('107', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('108', plain,
% 0.39/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('109', plain,
% 0.39/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('110', plain,
% 0.39/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('111', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('112', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_tsep_1 @ sk_D @ X0)
% 0.39/0.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.60          | (v1_tsep_1 @ sk_C @ X0)
% 0.39/0.60          | ~ (l1_pre_topc @ X0)
% 0.39/0.60          | ~ (v2_pre_topc @ X0))),
% 0.39/0.60      inference('demod', [status(thm)],
% 0.39/0.60                ['99', '100', '106', '107', '108', '109', '110', '111'])).
% 0.39/0.60  thf('113', plain,
% 0.39/0.60      ((~ (l1_pre_topc @ sk_D)
% 0.39/0.60        | ~ (v2_pre_topc @ sk_D)
% 0.39/0.60        | ~ (l1_pre_topc @ sk_D)
% 0.39/0.60        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.39/0.60        | ~ (v1_tsep_1 @ sk_D @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['95', '112'])).
% 0.39/0.60  thf('114', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('115', plain, ((v2_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.60  thf('116', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('117', plain,
% 0.39/0.60      (((v1_tsep_1 @ sk_C @ sk_D) | ~ (v1_tsep_1 @ sk_D @ sk_D))),
% 0.39/0.60      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.39/0.60  thf('118', plain,
% 0.39/0.60      ((~ (l1_pre_topc @ sk_D)
% 0.39/0.60        | ~ (v2_pre_topc @ sk_D)
% 0.39/0.60        | ~ (l1_struct_0 @ sk_D)
% 0.39/0.60        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.39/0.60      inference('sup-', [status(thm)], ['94', '117'])).
% 0.39/0.60  thf('119', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('120', plain, ((v2_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.60  thf('121', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf(dt_l1_pre_topc, axiom,
% 0.39/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.60  thf('122', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.60  thf('123', plain, ((l1_struct_0 @ sk_D)),
% 0.39/0.60      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.60  thf('124', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.39/0.60      inference('demod', [status(thm)], ['118', '119', '120', '123'])).
% 0.39/0.60  thf('125', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_B)
% 0.39/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.39/0.60        | (v2_struct_0 @ sk_C)
% 0.39/0.60        | (v2_struct_0 @ sk_D))),
% 0.39/0.60      inference('demod', [status(thm)], ['73', '74', '77', '78', '124'])).
% 0.39/0.60  thf('126', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('127', plain,
% 0.39/0.60      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['125', '126'])).
% 0.39/0.60  thf('128', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.39/0.60      inference('clc', [status(thm)], ['127', '128'])).
% 0.39/0.60  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('131', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.60      inference('clc', [status(thm)], ['129', '130'])).
% 0.39/0.60  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
