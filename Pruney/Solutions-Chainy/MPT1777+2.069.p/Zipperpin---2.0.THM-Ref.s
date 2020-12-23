%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bVi3dQ3mKf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:37 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 379 expanded)
%              Number of leaves         :   39 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          : 1292 (10735 expanded)
%              Number of equality atoms :   16 ( 268 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( X32 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('22',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['38','43','44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('51',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ( v1_tsep_1 @ X15 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('56',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('64',plain,(
    ! [X8: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

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

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('80',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('85',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('86',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['77','83','84','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('91',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('92',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','88','89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','96','97'])).

thf('99',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['0','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bVi3dQ3mKf
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.92/2.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.92/2.15  % Solved by: fo/fo7.sh
% 1.92/2.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.15  % done 3098 iterations in 1.701s
% 1.92/2.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.92/2.15  % SZS output start Refutation
% 1.92/2.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.92/2.15  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.92/2.15  thf(sk_D_type, type, sk_D: $i).
% 1.92/2.15  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.92/2.15  thf(sk_G_type, type, sk_G: $i).
% 1.92/2.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.92/2.15  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.92/2.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.92/2.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.92/2.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.92/2.15  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.92/2.15  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.92/2.15  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.15  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.92/2.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.92/2.15  thf(sk_E_type, type, sk_E: $i).
% 1.92/2.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.92/2.15  thf(sk_F_type, type, sk_F: $i).
% 1.92/2.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.92/2.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.92/2.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.92/2.15  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.92/2.15  thf(sk_C_type, type, sk_C: $i).
% 1.92/2.15  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.92/2.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.92/2.15  thf(t88_tmap_1, conjecture,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.92/2.15             ( l1_pre_topc @ B ) ) =>
% 1.92/2.15           ( ![C:$i]:
% 1.92/2.15             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.92/2.15               ( ![D:$i]:
% 1.92/2.15                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.92/2.15                   ( ![E:$i]:
% 1.92/2.15                     ( ( ( v1_funct_1 @ E ) & 
% 1.92/2.15                         ( v1_funct_2 @
% 1.92/2.15                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.92/2.15                         ( m1_subset_1 @
% 1.92/2.15                           E @ 
% 1.92/2.15                           ( k1_zfmisc_1 @
% 1.92/2.15                             ( k2_zfmisc_1 @
% 1.92/2.15                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.92/2.15                       ( ( ( g1_pre_topc @
% 1.92/2.15                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.92/2.15                           ( D ) ) =>
% 1.92/2.15                         ( ![F:$i]:
% 1.92/2.15                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.92/2.15                             ( ![G:$i]:
% 1.92/2.15                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.92/2.15                                 ( ( ( ( F ) = ( G ) ) & 
% 1.92/2.15                                     ( r1_tmap_1 @
% 1.92/2.15                                       C @ B @ 
% 1.92/2.15                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.92/2.15                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.92/2.15  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.15    (~( ![A:$i]:
% 1.92/2.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.92/2.15            ( l1_pre_topc @ A ) ) =>
% 1.92/2.15          ( ![B:$i]:
% 1.92/2.15            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.92/2.15                ( l1_pre_topc @ B ) ) =>
% 1.92/2.15              ( ![C:$i]:
% 1.92/2.15                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.92/2.15                  ( ![D:$i]:
% 1.92/2.15                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.92/2.15                      ( ![E:$i]:
% 1.92/2.15                        ( ( ( v1_funct_1 @ E ) & 
% 1.92/2.15                            ( v1_funct_2 @
% 1.92/2.15                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.92/2.15                            ( m1_subset_1 @
% 1.92/2.15                              E @ 
% 1.92/2.15                              ( k1_zfmisc_1 @
% 1.92/2.15                                ( k2_zfmisc_1 @
% 1.92/2.15                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.92/2.15                          ( ( ( g1_pre_topc @
% 1.92/2.15                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.92/2.15                              ( D ) ) =>
% 1.92/2.15                            ( ![F:$i]:
% 1.92/2.15                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.92/2.15                                ( ![G:$i]:
% 1.92/2.15                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.92/2.15                                    ( ( ( ( F ) = ( G ) ) & 
% 1.92/2.15                                        ( r1_tmap_1 @
% 1.92/2.15                                          C @ B @ 
% 1.92/2.15                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.92/2.15                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.92/2.15    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.92/2.15  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('1', plain,
% 1.92/2.15      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.92/2.15        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('2', plain, (((sk_F) = (sk_G))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('3', plain,
% 1.92/2.15      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.92/2.15        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.92/2.15      inference('demod', [status(thm)], ['1', '2'])).
% 1.92/2.15  thf('4', plain,
% 1.92/2.15      ((m1_subset_1 @ sk_E @ 
% 1.92/2.15        (k1_zfmisc_1 @ 
% 1.92/2.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf(t86_tmap_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.92/2.15             ( l1_pre_topc @ B ) ) =>
% 1.92/2.15           ( ![C:$i]:
% 1.92/2.15             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.92/2.15               ( ![D:$i]:
% 1.92/2.15                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.92/2.15                   ( ![E:$i]:
% 1.92/2.15                     ( ( ( v1_funct_1 @ E ) & 
% 1.92/2.15                         ( v1_funct_2 @
% 1.92/2.15                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.92/2.15                         ( m1_subset_1 @
% 1.92/2.15                           E @ 
% 1.92/2.15                           ( k1_zfmisc_1 @
% 1.92/2.15                             ( k2_zfmisc_1 @
% 1.92/2.15                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.92/2.15                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.92/2.15                         ( ![F:$i]:
% 1.92/2.15                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.92/2.15                             ( ![G:$i]:
% 1.92/2.15                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.92/2.15                                 ( ( ( F ) = ( G ) ) =>
% 1.92/2.15                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.92/2.15                                     ( r1_tmap_1 @
% 1.92/2.15                                       C @ B @ 
% 1.92/2.15                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.92/2.15  thf('5', plain,
% 1.92/2.15      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.92/2.15         ((v2_struct_0 @ X28)
% 1.92/2.15          | ~ (v2_pre_topc @ X28)
% 1.92/2.15          | ~ (l1_pre_topc @ X28)
% 1.92/2.15          | (v2_struct_0 @ X29)
% 1.92/2.15          | ~ (m1_pre_topc @ X29 @ X30)
% 1.92/2.15          | ~ (v1_tsep_1 @ X31 @ X29)
% 1.92/2.15          | ~ (m1_pre_topc @ X31 @ X29)
% 1.92/2.15          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 1.92/2.15          | ((X32) != (X33))
% 1.92/2.15          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 1.92/2.15               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 1.92/2.15          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X32)
% 1.92/2.15          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 1.92/2.15          | ~ (m1_subset_1 @ X34 @ 
% 1.92/2.15               (k1_zfmisc_1 @ 
% 1.92/2.15                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 1.92/2.15          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 1.92/2.15          | ~ (v1_funct_1 @ X34)
% 1.92/2.15          | ~ (m1_pre_topc @ X31 @ X30)
% 1.92/2.15          | (v2_struct_0 @ X31)
% 1.92/2.15          | ~ (l1_pre_topc @ X30)
% 1.92/2.15          | ~ (v2_pre_topc @ X30)
% 1.92/2.15          | (v2_struct_0 @ X30))),
% 1.92/2.15      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.92/2.15  thf('6', plain,
% 1.92/2.15      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 1.92/2.15         ((v2_struct_0 @ X30)
% 1.92/2.15          | ~ (v2_pre_topc @ X30)
% 1.92/2.15          | ~ (l1_pre_topc @ X30)
% 1.92/2.15          | (v2_struct_0 @ X31)
% 1.92/2.15          | ~ (m1_pre_topc @ X31 @ X30)
% 1.92/2.15          | ~ (v1_funct_1 @ X34)
% 1.92/2.15          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 1.92/2.15          | ~ (m1_subset_1 @ X34 @ 
% 1.92/2.15               (k1_zfmisc_1 @ 
% 1.92/2.15                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 1.92/2.15          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 1.92/2.15          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 1.92/2.15          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 1.92/2.15               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 1.92/2.15          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 1.92/2.15          | ~ (m1_pre_topc @ X31 @ X29)
% 1.92/2.15          | ~ (v1_tsep_1 @ X31 @ X29)
% 1.92/2.15          | ~ (m1_pre_topc @ X29 @ X30)
% 1.92/2.15          | (v2_struct_0 @ X29)
% 1.92/2.15          | ~ (l1_pre_topc @ X28)
% 1.92/2.15          | ~ (v2_pre_topc @ X28)
% 1.92/2.15          | (v2_struct_0 @ X28))),
% 1.92/2.15      inference('simplify', [status(thm)], ['5'])).
% 1.92/2.15  thf('7', plain,
% 1.92/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.15         ((v2_struct_0 @ sk_B)
% 1.92/2.15          | ~ (v2_pre_topc @ sk_B)
% 1.92/2.15          | ~ (l1_pre_topc @ sk_B)
% 1.92/2.15          | (v2_struct_0 @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.92/2.15          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.92/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.92/2.15          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.92/2.15               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.92/2.15          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.92/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.92/2.15          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.92/2.15          | ~ (v1_funct_1 @ sk_E)
% 1.92/2.15          | ~ (m1_pre_topc @ X1 @ X0)
% 1.92/2.15          | (v2_struct_0 @ X1)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0)
% 1.92/2.15          | (v2_struct_0 @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['4', '6'])).
% 1.92/2.15  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('10', plain,
% 1.92/2.15      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('12', plain,
% 1.92/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.15         ((v2_struct_0 @ sk_B)
% 1.92/2.15          | (v2_struct_0 @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.92/2.15          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.92/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.92/2.15          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.92/2.15               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.92/2.15          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.92/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.92/2.15          | ~ (m1_pre_topc @ X1 @ X0)
% 1.92/2.15          | (v2_struct_0 @ X1)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0)
% 1.92/2.15          | (v2_struct_0 @ X0))),
% 1.92/2.15      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.92/2.15  thf('13', plain,
% 1.92/2.15      (((v2_struct_0 @ sk_A)
% 1.92/2.15        | ~ (v2_pre_topc @ sk_A)
% 1.92/2.15        | ~ (l1_pre_topc @ sk_A)
% 1.92/2.15        | (v2_struct_0 @ sk_C)
% 1.92/2.15        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.92/2.15        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.92/2.15        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.92/2.15        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.92/2.15        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.92/2.15        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.92/2.15        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.92/2.15        | (v2_struct_0 @ sk_D)
% 1.92/2.15        | (v2_struct_0 @ sk_B))),
% 1.92/2.15      inference('sup-', [status(thm)], ['3', '12'])).
% 1.92/2.15  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('18', plain, (((sk_F) = (sk_G))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.92/2.15      inference('demod', [status(thm)], ['17', '18'])).
% 1.92/2.15  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('21', plain,
% 1.92/2.15      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf(t2_tsep_1, axiom,
% 1.92/2.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.92/2.15  thf('22', plain,
% 1.92/2.15      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.92/2.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.92/2.15  thf(t65_pre_topc, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( l1_pre_topc @ A ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( l1_pre_topc @ B ) =>
% 1.92/2.15           ( ( m1_pre_topc @ A @ B ) <=>
% 1.92/2.15             ( m1_pre_topc @
% 1.92/2.15               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.92/2.15  thf('23', plain,
% 1.92/2.15      (![X6 : $i, X7 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X6)
% 1.92/2.15          | ~ (m1_pre_topc @ X7 @ X6)
% 1.92/2.15          | (m1_pre_topc @ X7 @ 
% 1.92/2.15             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.92/2.15          | ~ (l1_pre_topc @ X7))),
% 1.92/2.15      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.92/2.15  thf('24', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | (m1_pre_topc @ X0 @ 
% 1.92/2.15             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.92/2.15          | ~ (l1_pre_topc @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['22', '23'])).
% 1.92/2.15  thf('25', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         ((m1_pre_topc @ X0 @ 
% 1.92/2.15           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.92/2.15          | ~ (l1_pre_topc @ X0))),
% 1.92/2.15      inference('simplify', [status(thm)], ['24'])).
% 1.92/2.15  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup+', [status(thm)], ['21', '25'])).
% 1.92/2.15  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf(dt_m1_pre_topc, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( l1_pre_topc @ A ) =>
% 1.92/2.15       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.92/2.15  thf('28', plain,
% 1.92/2.15      (![X4 : $i, X5 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.92/2.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.92/2.15  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['27', '28'])).
% 1.92/2.15  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.92/2.15      inference('demod', [status(thm)], ['26', '31'])).
% 1.92/2.15  thf('33', plain,
% 1.92/2.15      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('34', plain,
% 1.92/2.15      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.92/2.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.92/2.15  thf('35', plain,
% 1.92/2.15      (![X6 : $i, X7 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X6)
% 1.92/2.15          | ~ (m1_pre_topc @ X7 @ 
% 1.92/2.15               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.92/2.15          | (m1_pre_topc @ X7 @ X6)
% 1.92/2.15          | ~ (l1_pre_topc @ X7))),
% 1.92/2.15      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.92/2.15  thf('36', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ 
% 1.92/2.15             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.92/2.15          | ~ (l1_pre_topc @ 
% 1.92/2.15               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.92/2.15          | (m1_pre_topc @ 
% 1.92/2.15             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['34', '35'])).
% 1.92/2.15  thf('37', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X0)
% 1.92/2.15          | (m1_pre_topc @ 
% 1.92/2.15             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ 
% 1.92/2.15               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.92/2.15      inference('simplify', [status(thm)], ['36'])).
% 1.92/2.15  thf('38', plain,
% 1.92/2.15      ((~ (l1_pre_topc @ sk_D)
% 1.92/2.15        | (m1_pre_topc @ 
% 1.92/2.15           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 1.92/2.15        | ~ (l1_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['33', '37'])).
% 1.92/2.15  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('40', plain,
% 1.92/2.15      (![X4 : $i, X5 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.92/2.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.92/2.15  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.92/2.15      inference('sup-', [status(thm)], ['39', '40'])).
% 1.92/2.15  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('43', plain, ((l1_pre_topc @ sk_D)),
% 1.92/2.15      inference('demod', [status(thm)], ['41', '42'])).
% 1.92/2.15  thf('44', plain,
% 1.92/2.15      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['38', '43', '44', '45'])).
% 1.92/2.15  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.92/2.15      inference('demod', [status(thm)], ['26', '31'])).
% 1.92/2.15  thf(t35_borsuk_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( l1_pre_topc @ A ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( m1_pre_topc @ B @ A ) =>
% 1.92/2.15           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.92/2.15  thf('48', plain,
% 1.92/2.15      (![X23 : $i, X24 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X23 @ X24)
% 1.92/2.15          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 1.92/2.15          | ~ (l1_pre_topc @ X24))),
% 1.92/2.15      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.92/2.15  thf('49', plain,
% 1.92/2.15      ((~ (l1_pre_topc @ sk_D)
% 1.92/2.15        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 1.92/2.15      inference('sup-', [status(thm)], ['47', '48'])).
% 1.92/2.15  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 1.92/2.15      inference('demod', [status(thm)], ['41', '42'])).
% 1.92/2.15  thf('51', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 1.92/2.15      inference('demod', [status(thm)], ['49', '50'])).
% 1.92/2.15  thf(t19_tsep_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.92/2.15           ( ![C:$i]:
% 1.92/2.15             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.92/2.15               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 1.92/2.15                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 1.92/2.15  thf('52', plain,
% 1.92/2.15      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.92/2.15         (~ (v1_tsep_1 @ X15 @ X16)
% 1.92/2.15          | ~ (m1_pre_topc @ X15 @ X16)
% 1.92/2.15          | ~ (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))
% 1.92/2.15          | (v1_tsep_1 @ X15 @ X17)
% 1.92/2.15          | ~ (m1_pre_topc @ X17 @ X16)
% 1.92/2.15          | (v2_struct_0 @ X17)
% 1.92/2.15          | ~ (l1_pre_topc @ X16)
% 1.92/2.15          | ~ (v2_pre_topc @ X16)
% 1.92/2.15          | (v2_struct_0 @ X16))),
% 1.92/2.15      inference('cnf', [status(esa)], [t19_tsep_1])).
% 1.92/2.15  thf('53', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         ((v2_struct_0 @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | (v2_struct_0 @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.92/2.15          | (v1_tsep_1 @ sk_C @ sk_D)
% 1.92/2.15          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.92/2.15          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['51', '52'])).
% 1.92/2.15  thf('54', plain,
% 1.92/2.15      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 1.92/2.15        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.92/2.15        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.92/2.15        | (v2_struct_0 @ sk_D)
% 1.92/2.15        | ~ (l1_pre_topc @ sk_C)
% 1.92/2.15        | ~ (v2_pre_topc @ sk_C)
% 1.92/2.15        | (v2_struct_0 @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['46', '53'])).
% 1.92/2.15  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.92/2.15      inference('demod', [status(thm)], ['26', '31'])).
% 1.92/2.15  thf('56', plain,
% 1.92/2.15      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('57', plain,
% 1.92/2.15      (![X6 : $i, X7 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X6)
% 1.92/2.15          | ~ (m1_pre_topc @ X7 @ 
% 1.92/2.15               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.92/2.15          | (m1_pre_topc @ X7 @ X6)
% 1.92/2.15          | ~ (l1_pre_topc @ X7))),
% 1.92/2.15      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.92/2.15  thf('58', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | (m1_pre_topc @ X0 @ sk_C)
% 1.92/2.15          | ~ (l1_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['56', '57'])).
% 1.92/2.15  thf('59', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('60', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | (m1_pre_topc @ X0 @ sk_C))),
% 1.92/2.15      inference('demod', [status(thm)], ['58', '59'])).
% 1.92/2.15  thf('61', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['55', '60'])).
% 1.92/2.15  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['61', '62'])).
% 1.92/2.15  thf(fc10_tops_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.92/2.15  thf('64', plain,
% 1.92/2.15      (![X8 : $i]:
% 1.92/2.15         ((v3_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 1.92/2.15          | ~ (l1_pre_topc @ X8)
% 1.92/2.15          | ~ (v2_pre_topc @ X8))),
% 1.92/2.15      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.92/2.15  thf(d3_struct_0, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.92/2.15  thf('65', plain,
% 1.92/2.15      (![X2 : $i]:
% 1.92/2.15         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 1.92/2.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.92/2.15  thf('66', plain,
% 1.92/2.15      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.92/2.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.92/2.15  thf(t1_tsep_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( l1_pre_topc @ A ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( m1_pre_topc @ B @ A ) =>
% 1.92/2.15           ( m1_subset_1 @
% 1.92/2.15             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.92/2.15  thf('67', plain,
% 1.92/2.15      (![X18 : $i, X19 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X18 @ X19)
% 1.92/2.15          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 1.92/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.92/2.15          | ~ (l1_pre_topc @ X19))),
% 1.92/2.15      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.92/2.15  thf('68', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.92/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.92/2.15      inference('sup-', [status(thm)], ['66', '67'])).
% 1.92/2.15  thf('69', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.92/2.15           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.92/2.15          | ~ (l1_pre_topc @ X0))),
% 1.92/2.15      inference('simplify', [status(thm)], ['68'])).
% 1.92/2.15  thf(t16_tsep_1, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( ![B:$i]:
% 1.92/2.15         ( ( m1_pre_topc @ B @ A ) =>
% 1.92/2.15           ( ![C:$i]:
% 1.92/2.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.15               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.92/2.15                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.92/2.15                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.92/2.15  thf('70', plain,
% 1.92/2.15      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X12 @ X13)
% 1.92/2.15          | ((X14) != (u1_struct_0 @ X12))
% 1.92/2.15          | ~ (v3_pre_topc @ X14 @ X13)
% 1.92/2.15          | (v1_tsep_1 @ X12 @ X13)
% 1.92/2.15          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.92/2.15          | ~ (l1_pre_topc @ X13)
% 1.92/2.15          | ~ (v2_pre_topc @ X13))),
% 1.92/2.15      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.92/2.15  thf('71', plain,
% 1.92/2.15      (![X12 : $i, X13 : $i]:
% 1.92/2.15         (~ (v2_pre_topc @ X13)
% 1.92/2.15          | ~ (l1_pre_topc @ X13)
% 1.92/2.15          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.92/2.15               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.92/2.15          | (v1_tsep_1 @ X12 @ X13)
% 1.92/2.15          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 1.92/2.15          | ~ (m1_pre_topc @ X12 @ X13))),
% 1.92/2.15      inference('simplify', [status(thm)], ['70'])).
% 1.92/2.15  thf('72', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (m1_pre_topc @ X0 @ X0)
% 1.92/2.15          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.92/2.15          | (v1_tsep_1 @ X0 @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['69', '71'])).
% 1.92/2.15  thf('73', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (v2_pre_topc @ X0)
% 1.92/2.15          | (v1_tsep_1 @ X0 @ X0)
% 1.92/2.15          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.92/2.15          | ~ (m1_pre_topc @ X0 @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0))),
% 1.92/2.15      inference('simplify', [status(thm)], ['72'])).
% 1.92/2.15  thf('74', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.92/2.15          | ~ (l1_struct_0 @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (m1_pre_topc @ X0 @ X0)
% 1.92/2.15          | (v1_tsep_1 @ X0 @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['65', '73'])).
% 1.92/2.15  thf('75', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (v2_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0)
% 1.92/2.15          | (v1_tsep_1 @ X0 @ X0)
% 1.92/2.15          | ~ (m1_pre_topc @ X0 @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_struct_0 @ X0))),
% 1.92/2.15      inference('sup-', [status(thm)], ['64', '74'])).
% 1.92/2.15  thf('76', plain,
% 1.92/2.15      (![X0 : $i]:
% 1.92/2.15         (~ (l1_struct_0 @ X0)
% 1.92/2.15          | ~ (m1_pre_topc @ X0 @ X0)
% 1.92/2.15          | (v1_tsep_1 @ X0 @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X0)
% 1.92/2.15          | ~ (v2_pre_topc @ X0))),
% 1.92/2.15      inference('simplify', [status(thm)], ['75'])).
% 1.92/2.15  thf('77', plain,
% 1.92/2.15      ((~ (v2_pre_topc @ sk_C)
% 1.92/2.15        | ~ (l1_pre_topc @ sk_C)
% 1.92/2.15        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.92/2.15        | ~ (l1_struct_0 @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['63', '76'])).
% 1.92/2.15  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf(cc1_pre_topc, axiom,
% 1.92/2.15    (![A:$i]:
% 1.92/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.15       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.92/2.15  thf('79', plain,
% 1.92/2.15      (![X0 : $i, X1 : $i]:
% 1.92/2.15         (~ (m1_pre_topc @ X0 @ X1)
% 1.92/2.15          | (v2_pre_topc @ X0)
% 1.92/2.15          | ~ (l1_pre_topc @ X1)
% 1.92/2.15          | ~ (v2_pre_topc @ X1))),
% 1.92/2.15      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.92/2.15  thf('80', plain,
% 1.92/2.15      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.92/2.15      inference('sup-', [status(thm)], ['78', '79'])).
% 1.92/2.15  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('83', plain, ((v2_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.92/2.15  thf('84', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('85', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf(dt_l1_pre_topc, axiom,
% 1.92/2.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.92/2.15  thf('86', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.92/2.15      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.92/2.15  thf('87', plain, ((l1_struct_0 @ sk_C)),
% 1.92/2.15      inference('sup-', [status(thm)], ['85', '86'])).
% 1.92/2.15  thf('88', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['77', '83', '84', '87'])).
% 1.92/2.15  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['61', '62'])).
% 1.92/2.15  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['29', '30'])).
% 1.92/2.15  thf('91', plain, ((v2_pre_topc @ sk_C)),
% 1.92/2.15      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.92/2.15  thf('92', plain,
% 1.92/2.15      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.92/2.15      inference('demod', [status(thm)], ['54', '88', '89', '90', '91'])).
% 1.92/2.15  thf('93', plain, (~ (v2_struct_0 @ sk_D)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('94', plain, (((v2_struct_0 @ sk_C) | (v1_tsep_1 @ sk_C @ sk_D))),
% 1.92/2.15      inference('clc', [status(thm)], ['92', '93'])).
% 1.92/2.15  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('96', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.92/2.15      inference('clc', [status(thm)], ['94', '95'])).
% 1.92/2.15  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('98', plain,
% 1.92/2.15      (((v2_struct_0 @ sk_A)
% 1.92/2.15        | (v2_struct_0 @ sk_C)
% 1.92/2.15        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.92/2.15        | (v2_struct_0 @ sk_D)
% 1.92/2.15        | (v2_struct_0 @ sk_B))),
% 1.92/2.15      inference('demod', [status(thm)],
% 1.92/2.15                ['13', '14', '15', '16', '19', '20', '32', '96', '97'])).
% 1.92/2.15  thf('99', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('100', plain,
% 1.92/2.15      (((v2_struct_0 @ sk_B)
% 1.92/2.15        | (v2_struct_0 @ sk_D)
% 1.92/2.15        | (v2_struct_0 @ sk_C)
% 1.92/2.15        | (v2_struct_0 @ sk_A))),
% 1.92/2.15      inference('sup-', [status(thm)], ['98', '99'])).
% 1.92/2.15  thf('101', plain, (~ (v2_struct_0 @ sk_D)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('102', plain,
% 1.92/2.15      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 1.92/2.15      inference('sup-', [status(thm)], ['100', '101'])).
% 1.92/2.15  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('104', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.92/2.15      inference('clc', [status(thm)], ['102', '103'])).
% 1.92/2.15  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 1.92/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.15  thf('106', plain, ((v2_struct_0 @ sk_C)),
% 1.92/2.15      inference('clc', [status(thm)], ['104', '105'])).
% 1.92/2.15  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 1.92/2.15  
% 1.92/2.15  % SZS output end Refutation
% 1.92/2.15  
% 1.92/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
