%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lw3bwgzgyC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:36 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 587 expanded)
%              Number of leaves         :   42 ( 189 expanded)
%              Depth                    :   24
%              Number of atoms          : 2094 (18502 expanded)
%              Number of equality atoms :   35 ( 477 expanded)
%              Maximal formula depth    :   28 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
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

thf('9',plain,(
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('21',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
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

thf('33',plain,(
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

thf('34',plain,(
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
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','40','45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['25','30'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['4','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) )
                                 => ( r1_tmap_1 @ C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X35 @ ( k2_tmap_1 @ X37 @ X35 @ X40 @ X36 ) @ X39 )
      | ( X39 != X41 )
      | ( r1_tmap_1 @ X38 @ X35 @ ( k2_tmap_1 @ X37 @ X35 @ X40 @ X38 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t82_tmap_1])).

thf('65',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X38 ) )
      | ( r1_tmap_1 @ X38 @ X35 @ ( k2_tmap_1 @ X37 @ X35 @ X40 @ X38 ) @ X41 )
      | ~ ( r1_tmap_1 @ X36 @ X35 @ ( k2_tmap_1 @ X37 @ X35 @ X40 @ X36 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('72',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

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
    inference(demod,[status(thm)],['25','30'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','79'])).

thf('81',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('87',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('89',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('94',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','89','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( v1_tsep_1 @ X27 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ( r1_tmap_1 @ X26 @ X29 @ X30 @ X31 )
      | ( X31 != X28 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('101',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ X29 @ X30 @ X28 )
      | ~ ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_tsep_1 @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('104',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
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
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('114',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('115',plain,(
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

thf('116',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('118',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

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

thf('121',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('122',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('130',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('131',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('132',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('133',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['128','129','130','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['110','111','112','113','134'])).

thf('136',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lw3bwgzgyC
% 0.12/0.31  % Computer   : n007.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 19:34:06 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  % Running portfolio for 600 s
% 0.12/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.31  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.32  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 338 iterations in 0.171s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.60  thf(t88_tmap_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                         ( v1_funct_2 @
% 0.41/0.60                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                         ( m1_subset_1 @
% 0.41/0.60                           E @ 
% 0.41/0.60                           ( k1_zfmisc_1 @
% 0.41/0.60                             ( k2_zfmisc_1 @
% 0.41/0.60                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                       ( ( ( g1_pre_topc @
% 0.41/0.60                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.41/0.60                           ( D ) ) =>
% 0.41/0.60                         ( ![F:$i]:
% 0.41/0.60                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                             ( ![G:$i]:
% 0.41/0.60                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.60                                 ( ( ( ( F ) = ( G ) ) & 
% 0.41/0.60                                     ( r1_tmap_1 @
% 0.41/0.60                                       C @ B @ 
% 0.41/0.60                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.41/0.60                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60            ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60                ( l1_pre_topc @ B ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60                  ( ![D:$i]:
% 0.41/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.60                      ( ![E:$i]:
% 0.41/0.60                        ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                            ( v1_funct_2 @
% 0.41/0.60                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                            ( m1_subset_1 @
% 0.41/0.60                              E @ 
% 0.41/0.60                              ( k1_zfmisc_1 @
% 0.41/0.60                                ( k2_zfmisc_1 @
% 0.41/0.60                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                          ( ( ( g1_pre_topc @
% 0.41/0.60                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.41/0.60                              ( D ) ) =>
% 0.41/0.60                            ( ![F:$i]:
% 0.41/0.60                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                                ( ![G:$i]:
% 0.41/0.60                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.60                                    ( ( ( ( F ) = ( G ) ) & 
% 0.41/0.60                                        ( r1_tmap_1 @
% 0.41/0.60                                          C @ B @ 
% 0.41/0.60                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.41/0.60                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.41/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.60        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('3', plain, (((sk_F) = (sk_G))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.60        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.41/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d5_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                         ( v1_funct_2 @
% 0.41/0.60                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                         ( m1_subset_1 @
% 0.41/0.60                           E @ 
% 0.41/0.60                           ( k1_zfmisc_1 @
% 0.41/0.60                             ( k2_zfmisc_1 @
% 0.41/0.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                       ( ( m1_pre_topc @ D @ C ) =>
% 0.41/0.60                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.41/0.60                           ( k2_partfun1 @
% 0.41/0.60                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.41/0.60                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X15)
% 0.41/0.60          | ~ (v2_pre_topc @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15)
% 0.41/0.60          | ~ (m1_pre_topc @ X16 @ X17)
% 0.41/0.60          | ~ (m1_pre_topc @ X16 @ X18)
% 0.41/0.60          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.41/0.60                 X19 @ (u1_struct_0 @ X16)))
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.41/0.60          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.41/0.60          | ~ (v1_funct_1 @ X19)
% 0.41/0.60          | ~ (m1_pre_topc @ X18 @ X17)
% 0.41/0.60          | ~ (l1_pre_topc @ X17)
% 0.41/0.60          | ~ (v2_pre_topc @ X17)
% 0.41/0.60          | (v2_struct_0 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X1)))
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X1)))
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60          | (v2_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '14'])).
% 0.41/0.60  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | (v2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               sk_E @ (u1_struct_0 @ sk_C)))
% 0.41/0.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t2_tsep_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.60  thf(t65_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ( m1_pre_topc @ A @ B ) <=>
% 0.41/0.60             ( m1_pre_topc @
% 0.41/0.60               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X8)
% 0.41/0.60          | ~ (m1_pre_topc @ X9 @ X8)
% 0.41/0.60          | (m1_pre_topc @ X9 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.41/0.60          | ~ (l1_pre_topc @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | (m1_pre_topc @ X0 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_pre_topc @ X0 @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.60  thf('25', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['20', '24'])).
% 0.41/0.60  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_m1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('28', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d4_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                 ( m1_subset_1 @
% 0.41/0.60                   C @ 
% 0.41/0.60                   ( k1_zfmisc_1 @
% 0.41/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.41/0.60                     ( k2_partfun1 @
% 0.41/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.41/0.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X11)
% 0.41/0.60          | ~ (v2_pre_topc @ X11)
% 0.41/0.60          | ~ (l1_pre_topc @ X11)
% 0.41/0.60          | ~ (m1_pre_topc @ X12 @ X13)
% 0.41/0.60          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.41/0.60                 X14 @ (u1_struct_0 @ X12)))
% 0.41/0.60          | ~ (m1_subset_1 @ X14 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.41/0.60          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.41/0.60          | ~ (v1_funct_1 @ X14)
% 0.41/0.60          | ~ (l1_pre_topc @ X13)
% 0.41/0.60          | ~ (v2_pre_topc @ X13)
% 0.41/0.60          | (v2_struct_0 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.60          | (v2_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X1)
% 0.41/0.60          | ~ (v2_pre_topc @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.41/0.60  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('43', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('45', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['34', '40', '45', '46', '47', '48', '49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               sk_E @ (u1_struct_0 @ sk_C)))
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['31', '50'])).
% 0.41/0.60  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_D)
% 0.41/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.41/0.60      inference('clc', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.41/0.60            (u1_struct_0 @ sk_C)))),
% 0.41/0.60      inference('clc', [status(thm)], ['53', '54'])).
% 0.41/0.60  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '30'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.60            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '55', '56'])).
% 0.41/0.60  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.60            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.41/0.60      inference('clc', [status(thm)], ['57', '58'])).
% 0.41/0.60  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.60         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.41/0.60      inference('clc', [status(thm)], ['59', '60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.41/0.60        sk_F)),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '61'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t82_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                         ( v1_funct_2 @
% 0.41/0.60                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                         ( m1_subset_1 @
% 0.41/0.60                           E @ 
% 0.41/0.60                           ( k1_zfmisc_1 @
% 0.41/0.60                             ( k2_zfmisc_1 @
% 0.41/0.60                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                       ( ( m1_pre_topc @ C @ D ) =>
% 0.41/0.60                         ( ![F:$i]:
% 0.41/0.60                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                             ( ![G:$i]:
% 0.41/0.60                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.60                                 ( ( ( ( F ) = ( G ) ) & 
% 0.41/0.60                                     ( r1_tmap_1 @
% 0.41/0.60                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.41/0.60                                       F ) ) =>
% 0.41/0.60                                   ( r1_tmap_1 @
% 0.41/0.60                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X35)
% 0.41/0.60          | ~ (v2_pre_topc @ X35)
% 0.41/0.60          | ~ (l1_pre_topc @ X35)
% 0.41/0.60          | (v2_struct_0 @ X36)
% 0.41/0.60          | ~ (m1_pre_topc @ X36 @ X37)
% 0.41/0.60          | ~ (m1_pre_topc @ X38 @ X36)
% 0.41/0.60          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.41/0.60          | ~ (r1_tmap_1 @ X36 @ X35 @ (k2_tmap_1 @ X37 @ X35 @ X40 @ X36) @ 
% 0.41/0.60               X39)
% 0.41/0.60          | ((X39) != (X41))
% 0.41/0.60          | (r1_tmap_1 @ X38 @ X35 @ (k2_tmap_1 @ X37 @ X35 @ X40 @ X38) @ X41)
% 0.41/0.60          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.41/0.60          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 0.41/0.60          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 0.41/0.60          | ~ (v1_funct_1 @ X40)
% 0.41/0.60          | ~ (m1_pre_topc @ X38 @ X37)
% 0.41/0.60          | (v2_struct_0 @ X38)
% 0.41/0.60          | ~ (l1_pre_topc @ X37)
% 0.41/0.60          | ~ (v2_pre_topc @ X37)
% 0.41/0.60          | (v2_struct_0 @ X37))),
% 0.41/0.60      inference('cnf', [status(esa)], [t82_tmap_1])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i, X41 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X37)
% 0.41/0.60          | ~ (v2_pre_topc @ X37)
% 0.41/0.60          | ~ (l1_pre_topc @ X37)
% 0.41/0.60          | (v2_struct_0 @ X38)
% 0.41/0.60          | ~ (m1_pre_topc @ X38 @ X37)
% 0.41/0.60          | ~ (v1_funct_1 @ X40)
% 0.41/0.60          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 0.41/0.60          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 0.41/0.60          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X38))
% 0.41/0.60          | (r1_tmap_1 @ X38 @ X35 @ (k2_tmap_1 @ X37 @ X35 @ X40 @ X38) @ X41)
% 0.41/0.60          | ~ (r1_tmap_1 @ X36 @ X35 @ (k2_tmap_1 @ X37 @ X35 @ X40 @ X36) @ 
% 0.41/0.60               X41)
% 0.41/0.60          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X36))
% 0.41/0.60          | ~ (m1_pre_topc @ X38 @ X36)
% 0.41/0.60          | ~ (m1_pre_topc @ X36 @ X37)
% 0.41/0.60          | (v2_struct_0 @ X36)
% 0.41/0.60          | ~ (l1_pre_topc @ X35)
% 0.41/0.60          | ~ (v2_pre_topc @ X35)
% 0.41/0.60          | (v2_struct_0 @ X35))),
% 0.41/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60               X2)
% 0.41/0.60          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ X2)
% 0.41/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.41/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X1)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['63', '65'])).
% 0.41/0.60  thf('67', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('72', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60               X2)
% 0.41/0.60          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ X2)
% 0.41/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.41/0.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X1)
% 0.41/0.60          | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['66', '67', '68', '69', '70', '71', '72'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.41/0.60          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60             sk_F)
% 0.41/0.60          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ sk_C)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['62', '73'])).
% 0.41/0.60  thf('75', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('76', plain, (((sk_F) = (sk_G))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('77', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.41/0.60  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '30'])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.41/0.60          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60             sk_F)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.41/0.60          | (v2_struct_0 @ sk_C)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['74', '77', '78'])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.41/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) @ 
% 0.41/0.60           sk_F)
% 0.41/0.60        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '79'])).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.60  thf(t59_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @
% 0.41/0.60             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.41/0.60           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X6 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.41/0.60          | (m1_pre_topc @ X6 @ X7)
% 0.41/0.60          | ~ (l1_pre_topc @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | (m1_pre_topc @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.60        | (m1_pre_topc @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['81', '84'])).
% 0.41/0.60  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('88', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('89', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.41/0.60  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X8)
% 0.41/0.60          | ~ (m1_pre_topc @ X9 @ X8)
% 0.41/0.60          | (m1_pre_topc @ X9 @ 
% 0.41/0.60             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.41/0.60          | ~ (l1_pre_topc @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.60        | (m1_pre_topc @ sk_D @ 
% 0.41/0.60           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['90', '91'])).
% 0.41/0.60  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('94', plain,
% 0.41/0.60      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('95', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.41/0.60  thf('97', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) @ 
% 0.41/0.60           sk_F)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('demod', [status(thm)], ['80', '89', '96'])).
% 0.41/0.60  thf('98', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_D)
% 0.41/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) @ 
% 0.41/0.60           sk_F)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('simplify', [status(thm)], ['97'])).
% 0.41/0.60  thf('99', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t67_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.60                 ( m1_subset_1 @
% 0.41/0.60                   C @ 
% 0.41/0.60                   ( k1_zfmisc_1 @
% 0.41/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.41/0.60                     ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.60                       ( ![F:$i]:
% 0.41/0.60                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.60                           ( ( ( E ) = ( F ) ) =>
% 0.41/0.60                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.41/0.60                               ( r1_tmap_1 @
% 0.41/0.60                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('100', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X26)
% 0.41/0.60          | ~ (v2_pre_topc @ X26)
% 0.41/0.60          | ~ (l1_pre_topc @ X26)
% 0.41/0.60          | (v2_struct_0 @ X27)
% 0.41/0.60          | ~ (v1_tsep_1 @ X27 @ X26)
% 0.41/0.60          | ~ (m1_pre_topc @ X27 @ X26)
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.41/0.60          | ~ (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ 
% 0.41/0.60               X28)
% 0.41/0.60          | (r1_tmap_1 @ X26 @ X29 @ X30 @ X31)
% 0.41/0.60          | ((X31) != (X28))
% 0.41/0.60          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.41/0.60          | ~ (m1_subset_1 @ X30 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.41/0.60          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.41/0.60          | ~ (v1_funct_1 @ X30)
% 0.41/0.60          | ~ (l1_pre_topc @ X29)
% 0.41/0.60          | ~ (v2_pre_topc @ X29)
% 0.41/0.60          | (v2_struct_0 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.41/0.60  thf('101', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X29)
% 0.41/0.60          | ~ (v2_pre_topc @ X29)
% 0.41/0.60          | ~ (l1_pre_topc @ X29)
% 0.41/0.60          | ~ (v1_funct_1 @ X30)
% 0.41/0.60          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.41/0.60          | ~ (m1_subset_1 @ X30 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.41/0.60          | (r1_tmap_1 @ X26 @ X29 @ X30 @ X28)
% 0.41/0.60          | ~ (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ 
% 0.41/0.60               X28)
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.41/0.60          | ~ (m1_pre_topc @ X27 @ X26)
% 0.41/0.60          | ~ (v1_tsep_1 @ X27 @ X26)
% 0.41/0.60          | (v2_struct_0 @ X27)
% 0.41/0.60          | ~ (l1_pre_topc @ X26)
% 0.41/0.60          | ~ (v2_pre_topc @ X26)
% 0.41/0.60          | (v2_struct_0 @ X26))),
% 0.41/0.60      inference('simplify', [status(thm)], ['100'])).
% 0.41/0.60  thf('102', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60               X1)
% 0.41/0.60          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.41/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['99', '101'])).
% 0.41/0.60  thf('103', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.41/0.60  thf('104', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('105', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('108', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('109', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.60          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.41/0.60               X1)
% 0.41/0.60          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.41/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['102', '103', '104', '105', '106', '107', '108'])).
% 0.41/0.60  thf('110', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_B)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.41/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.60        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.41/0.60        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.41/0.60        | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['98', '109'])).
% 0.41/0.60  thf('111', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('112', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('113', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.41/0.60  thf('114', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.41/0.60  thf(fc10_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.41/0.60  thf('115', plain,
% 0.41/0.60      (![X10 : $i]:
% 0.41/0.60         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.41/0.60          | ~ (l1_pre_topc @ X10)
% 0.41/0.60          | ~ (v2_pre_topc @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.41/0.60  thf(d3_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.60  thf('116', plain,
% 0.41/0.60      (![X2 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('117', plain,
% 0.41/0.60      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.60  thf(t1_tsep_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( m1_subset_1 @
% 0.41/0.60             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('118', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X23 @ X24)
% 0.41/0.60          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.41/0.60          | ~ (l1_pre_topc @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.60  thf('119', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['117', '118'])).
% 0.41/0.60  thf('120', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['119'])).
% 0.41/0.60  thf(t16_tsep_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.60                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.60                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('121', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X20 @ X21)
% 0.41/0.60          | ((X22) != (u1_struct_0 @ X20))
% 0.41/0.60          | ~ (v3_pre_topc @ X22 @ X21)
% 0.41/0.60          | (v1_tsep_1 @ X20 @ X21)
% 0.41/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.60          | ~ (l1_pre_topc @ X21)
% 0.41/0.60          | ~ (v2_pre_topc @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.60  thf('122', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (v2_pre_topc @ X21)
% 0.41/0.60          | ~ (l1_pre_topc @ X21)
% 0.41/0.60          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.41/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.60          | (v1_tsep_1 @ X20 @ X21)
% 0.41/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.41/0.60          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.41/0.60      inference('simplify', [status(thm)], ['121'])).
% 0.41/0.60  thf('123', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['120', '122'])).
% 0.41/0.60  thf('124', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_pre_topc @ X0)
% 0.41/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.60          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['123'])).
% 0.41/0.60  thf('125', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['116', '124'])).
% 0.41/0.60  thf('126', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v2_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0)
% 0.41/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['115', '125'])).
% 0.41/0.60  thf('127', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.60          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0)
% 0.41/0.60          | ~ (v2_pre_topc @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['126'])).
% 0.41/0.60  thf('128', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_D)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_D)
% 0.41/0.60        | (v1_tsep_1 @ sk_D @ sk_D)
% 0.41/0.60        | ~ (l1_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['114', '127'])).
% 0.41/0.60  thf('129', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.41/0.60  thf('130', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('131', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf(dt_l1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.60  thf('132', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('133', plain, ((l1_struct_0 @ sk_D)),
% 0.41/0.60      inference('sup-', [status(thm)], ['131', '132'])).
% 0.41/0.60  thf('134', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['128', '129', '130', '133'])).
% 0.41/0.60  thf('135', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_B)
% 0.41/0.60        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('demod', [status(thm)], ['110', '111', '112', '113', '134'])).
% 0.41/0.60  thf('136', plain,
% 0.41/0.60      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.60        | (v2_struct_0 @ sk_D)
% 0.41/0.60        | (v2_struct_0 @ sk_C)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('simplify', [status(thm)], ['135'])).
% 0.41/0.60  thf('137', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('138', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['136', '137'])).
% 0.41/0.61  thf('139', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('140', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.41/0.61      inference('clc', [status(thm)], ['138', '139'])).
% 0.41/0.61  thf('141', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('142', plain, ((v2_struct_0 @ sk_C)),
% 0.41/0.61      inference('clc', [status(thm)], ['140', '141'])).
% 0.41/0.61  thf('143', plain, ($false), inference('demod', [status(thm)], ['0', '142'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.47/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
