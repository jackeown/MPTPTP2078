%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AC02MHRiWx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 406 expanded)
%              Number of leaves         :   40 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          : 1331 (11567 expanded)
%              Number of equality atoms :   16 ( 290 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('6',plain,(
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
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('47',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('55',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('60',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['51','52','58','59'])).

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

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ( v1_tsep_1 @ X14 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('65',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['64','69'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('71',plain,(
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

thf('72',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

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

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('86',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('88',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['84','85','86','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['64','69'])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('93',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('94',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['63','90','91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','98','99'])).

thf('101',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AC02MHRiWx
% 0.16/0.35  % Computer   : n010.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 14:40:15 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 402 iterations in 0.188s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.66  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.66  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.66  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.66  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.66  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.66  thf(t88_tmap_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.66             ( l1_pre_topc @ B ) ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.66               ( ![D:$i]:
% 0.45/0.66                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.66                   ( ![E:$i]:
% 0.45/0.66                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66                         ( v1_funct_2 @
% 0.45/0.66                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.66                         ( m1_subset_1 @
% 0.45/0.66                           E @ 
% 0.45/0.66                           ( k1_zfmisc_1 @
% 0.45/0.66                             ( k2_zfmisc_1 @
% 0.45/0.66                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.66                       ( ( ( g1_pre_topc @
% 0.45/0.66                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.66                           ( D ) ) =>
% 0.45/0.66                         ( ![F:$i]:
% 0.45/0.66                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.66                             ( ![G:$i]:
% 0.45/0.66                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.66                                 ( ( ( ( F ) = ( G ) ) & 
% 0.45/0.66                                     ( r1_tmap_1 @
% 0.45/0.66                                       C @ B @ 
% 0.45/0.66                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.45/0.66                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.66            ( l1_pre_topc @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.66                ( l1_pre_topc @ B ) ) =>
% 0.45/0.66              ( ![C:$i]:
% 0.45/0.66                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.66                  ( ![D:$i]:
% 0.45/0.66                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.66                      ( ![E:$i]:
% 0.45/0.66                        ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66                            ( v1_funct_2 @
% 0.45/0.66                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.66                            ( m1_subset_1 @
% 0.45/0.66                              E @ 
% 0.45/0.66                              ( k1_zfmisc_1 @
% 0.45/0.66                                ( k2_zfmisc_1 @
% 0.45/0.66                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.66                          ( ( ( g1_pre_topc @
% 0.45/0.66                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.66                              ( D ) ) =>
% 0.45/0.66                            ( ![F:$i]:
% 0.45/0.66                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.66                                ( ![G:$i]:
% 0.45/0.66                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.66                                    ( ( ( ( F ) = ( G ) ) & 
% 0.45/0.66                                        ( r1_tmap_1 @
% 0.45/0.66                                          C @ B @ 
% 0.45/0.66                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.45/0.66                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.45/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.45/0.66        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('2', plain, (((sk_F) = (sk_G))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.45/0.66        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.45/0.66      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_E @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t86_tmap_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.66             ( l1_pre_topc @ B ) ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.66               ( ![D:$i]:
% 0.45/0.66                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.66                   ( ![E:$i]:
% 0.45/0.66                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66                         ( v1_funct_2 @
% 0.45/0.66                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.66                         ( m1_subset_1 @
% 0.45/0.66                           E @ 
% 0.45/0.66                           ( k1_zfmisc_1 @
% 0.45/0.66                             ( k2_zfmisc_1 @
% 0.45/0.66                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.66                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.45/0.66                         ( ![F:$i]:
% 0.45/0.66                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.66                             ( ![G:$i]:
% 0.45/0.66                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.66                                 ( ( ( F ) = ( G ) ) =>
% 0.45/0.66                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.45/0.66                                     ( r1_tmap_1 @
% 0.45/0.66                                       C @ B @ 
% 0.45/0.66                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.66         ((v2_struct_0 @ X26)
% 0.45/0.66          | ~ (v2_pre_topc @ X26)
% 0.45/0.66          | ~ (l1_pre_topc @ X26)
% 0.45/0.66          | (v2_struct_0 @ X27)
% 0.45/0.66          | ~ (m1_pre_topc @ X27 @ X28)
% 0.45/0.66          | ~ (v1_tsep_1 @ X29 @ X27)
% 0.45/0.66          | ~ (m1_pre_topc @ X29 @ X27)
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.45/0.66          | ((X30) != (X31))
% 0.45/0.66          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.45/0.66               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.45/0.66          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X30)
% 0.45/0.66          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.45/0.66          | ~ (m1_subset_1 @ X32 @ 
% 0.45/0.66               (k1_zfmisc_1 @ 
% 0.45/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.45/0.66          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.45/0.66          | ~ (v1_funct_1 @ X32)
% 0.45/0.66          | ~ (m1_pre_topc @ X29 @ X28)
% 0.45/0.66          | (v2_struct_0 @ X29)
% 0.45/0.66          | ~ (l1_pre_topc @ X28)
% 0.45/0.66          | ~ (v2_pre_topc @ X28)
% 0.45/0.66          | (v2_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.45/0.66         ((v2_struct_0 @ X28)
% 0.45/0.66          | ~ (v2_pre_topc @ X28)
% 0.45/0.66          | ~ (l1_pre_topc @ X28)
% 0.45/0.66          | (v2_struct_0 @ X29)
% 0.45/0.66          | ~ (m1_pre_topc @ X29 @ X28)
% 0.45/0.66          | ~ (v1_funct_1 @ X32)
% 0.45/0.66          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.45/0.66          | ~ (m1_subset_1 @ X32 @ 
% 0.45/0.66               (k1_zfmisc_1 @ 
% 0.45/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.45/0.66          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.45/0.66          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 0.45/0.66          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.45/0.66               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.45/0.66          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 0.45/0.66          | ~ (m1_pre_topc @ X29 @ X27)
% 0.45/0.66          | ~ (v1_tsep_1 @ X29 @ X27)
% 0.45/0.66          | ~ (m1_pre_topc @ X27 @ X28)
% 0.45/0.66          | (v2_struct_0 @ X27)
% 0.45/0.66          | ~ (l1_pre_topc @ X26)
% 0.45/0.66          | ~ (v2_pre_topc @ X26)
% 0.45/0.66          | (v2_struct_0 @ X26))),
% 0.45/0.66      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((v2_struct_0 @ sk_B)
% 0.45/0.66          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.66          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.66          | (v2_struct_0 @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.66          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.45/0.66          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.45/0.66               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.45/0.66          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.45/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.66          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.45/0.66          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.66          | (v2_struct_0 @ X1)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | (v2_struct_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.66  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((v2_struct_0 @ sk_B)
% 0.45/0.66          | (v2_struct_0 @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.66          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.45/0.66          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.45/0.66               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.45/0.66          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.45/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.66          | (v2_struct_0 @ X1)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | (v2_struct_0 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (v2_struct_0 @ sk_C)
% 0.45/0.66        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.66        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.45/0.66        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.45/0.66        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.45/0.66        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.45/0.66        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.45/0.66        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.66        | (v2_struct_0 @ sk_D)
% 0.45/0.66        | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '12'])).
% 0.45/0.66  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('18', plain, (((sk_F) = (sk_G))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.66  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t2_tsep_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.66  thf(t65_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( l1_pre_topc @ B ) =>
% 0.45/0.66           ( ( m1_pre_topc @ A @ B ) <=>
% 0.45/0.66             ( m1_pre_topc @
% 0.45/0.66               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X8)
% 0.45/0.66          | ~ (m1_pre_topc @ X9 @ X8)
% 0.45/0.66          | (m1_pre_topc @ X9 @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.45/0.66          | ~ (l1_pre_topc @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | (m1_pre_topc @ X0 @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.66          | ~ (l1_pre_topc @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((m1_pre_topc @ X0 @ 
% 0.45/0.66           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.66          | ~ (l1_pre_topc @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.66  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.45/0.66      inference('sup+', [status(thm)], ['21', '25'])).
% 0.45/0.66  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_m1_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.66  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '31'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.66  thf(t59_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_pre_topc @
% 0.45/0.66             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.45/0.66           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X6 @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.45/0.66          | (m1_pre_topc @ X6 @ X7)
% 0.45/0.66          | ~ (l1_pre_topc @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | (m1_pre_topc @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_D)
% 0.45/0.66        | (m1_pre_topc @ 
% 0.45/0.66           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '36'])).
% 0.45/0.66  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.66  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('42', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 0.45/0.66  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '31'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.66  thf(t4_tsep_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.66               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.45/0.66                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X20 @ X21)
% 0.45/0.66          | ~ (m1_pre_topc @ X20 @ X22)
% 0.45/0.66          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 0.45/0.66          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.66          | ~ (l1_pre_topc @ X21)
% 0.45/0.66          | ~ (v2_pre_topc @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.66          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.66          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.45/0.66          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['49'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_C)
% 0.45/0.66        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.45/0.66        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['46', '50'])).
% 0.45/0.66  thf('52', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc1_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.66          | (v2_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X1)
% 0.45/0.66          | ~ (v2_pre_topc @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('58', plain, ((v2_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.45/0.66  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 0.45/0.66  thf('60', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '52', '58', '59'])).
% 0.45/0.66  thf(t19_tsep_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.66               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.66                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (v1_tsep_1 @ X14 @ X15)
% 0.45/0.66          | ~ (m1_pre_topc @ X14 @ X15)
% 0.45/0.66          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 0.45/0.66          | (v1_tsep_1 @ X14 @ X16)
% 0.45/0.66          | ~ (m1_pre_topc @ X16 @ X15)
% 0.45/0.66          | (v2_struct_0 @ X16)
% 0.45/0.66          | ~ (l1_pre_topc @ X15)
% 0.45/0.66          | ~ (v2_pre_topc @ X15)
% 0.45/0.66          | (v2_struct_0 @ X15))),
% 0.45/0.66      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_struct_0 @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | (v2_struct_0 @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.66          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.45/0.66          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.45/0.66          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.45/0.66        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.45/0.66        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.45/0.66        | (v2_struct_0 @ sk_D)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_C)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_C)
% 0.45/0.66        | (v2_struct_0 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['45', '62'])).
% 0.45/0.66  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '31'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X6 @ 
% 0.45/0.66             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.45/0.66          | (m1_pre_topc @ X6 @ X7)
% 0.45/0.66          | ~ (l1_pre_topc @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.45/0.66          | ~ (l1_pre_topc @ sk_C)
% 0.45/0.66          | (m1_pre_topc @ X0 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '69'])).
% 0.45/0.66  thf(fc10_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X10 : $i]:
% 0.45/0.66         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.45/0.66          | ~ (l1_pre_topc @ X10)
% 0.45/0.66          | ~ (v2_pre_topc @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.66  thf(d3_struct_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X2 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.66  thf(t1_tsep_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.66           ( m1_subset_1 @
% 0.45/0.66             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X17 @ X18)
% 0.45/0.66          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (l1_pre_topc @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.66          | ~ (l1_pre_topc @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['75'])).
% 0.45/0.66  thf(t16_tsep_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.66                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.66                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X11 @ X12)
% 0.45/0.66          | ((X13) != (u1_struct_0 @ X11))
% 0.45/0.66          | ~ (v3_pre_topc @ X13 @ X12)
% 0.45/0.66          | (v1_tsep_1 @ X11 @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.66          | ~ (l1_pre_topc @ X12)
% 0.45/0.66          | ~ (v2_pre_topc @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         (~ (v2_pre_topc @ X12)
% 0.45/0.66          | ~ (l1_pre_topc @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.45/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.66          | (v1_tsep_1 @ X11 @ X12)
% 0.45/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.45/0.66          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.45/0.66      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X0)
% 0.45/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.66          | (v1_tsep_1 @ X0 @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['76', '78'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v2_pre_topc @ X0)
% 0.45/0.66          | (v1_tsep_1 @ X0 @ X0)
% 0.45/0.66          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['79'])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.45/0.66          | ~ (l1_struct_0 @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X0)
% 0.45/0.66          | (v1_tsep_1 @ X0 @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['72', '80'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v2_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0)
% 0.45/0.66          | (v1_tsep_1 @ X0 @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (l1_struct_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '81'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_struct_0 @ X0)
% 0.45/0.66          | ~ (m1_pre_topc @ X0 @ X0)
% 0.45/0.66          | (v1_tsep_1 @ X0 @ X0)
% 0.45/0.66          | ~ (l1_pre_topc @ X0)
% 0.45/0.66          | ~ (v2_pre_topc @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['82'])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      ((~ (v2_pre_topc @ sk_C)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_C)
% 0.45/0.66        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['70', '83'])).
% 0.45/0.66  thf('85', plain, ((v2_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.45/0.66  thf('86', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('87', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf(dt_l1_pre_topc, axiom,
% 0.45/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.66  thf('88', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.66  thf('89', plain, ((l1_struct_0 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.66  thf('90', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85', '86', '89'])).
% 0.45/0.66  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '69'])).
% 0.45/0.66  thf('92', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('93', plain, ((v2_pre_topc @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['63', '90', '91', '92', '93'])).
% 0.45/0.66  thf('95', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('96', plain, (((v2_struct_0 @ sk_C) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.45/0.66      inference('clc', [status(thm)], ['94', '95'])).
% 0.45/0.66  thf('97', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('98', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.45/0.66      inference('clc', [status(thm)], ['96', '97'])).
% 0.45/0.66  thf('99', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('100', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A)
% 0.45/0.66        | (v2_struct_0 @ sk_C)
% 0.45/0.66        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.45/0.66        | (v2_struct_0 @ sk_D)
% 0.45/0.66        | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['13', '14', '15', '16', '19', '20', '32', '98', '99'])).
% 0.45/0.66  thf('101', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('102', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_B)
% 0.45/0.66        | (v2_struct_0 @ sk_D)
% 0.45/0.66        | (v2_struct_0 @ sk_C)
% 0.45/0.66        | (v2_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.66  thf('103', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('104', plain,
% 0.45/0.66      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('106', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.45/0.66      inference('clc', [status(thm)], ['104', '105'])).
% 0.45/0.66  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('108', plain, ((v2_struct_0 @ sk_C)),
% 0.45/0.66      inference('clc', [status(thm)], ['106', '107'])).
% 0.45/0.66  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
