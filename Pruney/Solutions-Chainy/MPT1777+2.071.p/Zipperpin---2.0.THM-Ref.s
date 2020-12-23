%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sBkABLFWEh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:37 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 379 expanded)
%              Number of leaves         :   39 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          : 1292 (10735 expanded)
%              Number of equality atoms :   16 ( 268 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ( X29 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sBkABLFWEh
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.09/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.09/1.26  % Solved by: fo/fo7.sh
% 1.09/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.26  % done 1635 iterations in 0.805s
% 1.09/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.09/1.26  % SZS output start Refutation
% 1.09/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.09/1.26  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.09/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.26  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.09/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.09/1.26  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.09/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.09/1.26  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.09/1.26  thf(sk_D_type, type, sk_D: $i).
% 1.09/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.09/1.26  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.09/1.26  thf(sk_E_type, type, sk_E: $i).
% 1.09/1.26  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.09/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.09/1.26  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.09/1.26  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.09/1.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.09/1.26  thf(sk_C_type, type, sk_C: $i).
% 1.09/1.26  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.09/1.26  thf(sk_F_type, type, sk_F: $i).
% 1.09/1.26  thf(sk_G_type, type, sk_G: $i).
% 1.09/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.26  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.09/1.26  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.09/1.26  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.09/1.26  thf(t88_tmap_1, conjecture,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.26       ( ![B:$i]:
% 1.09/1.26         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.09/1.26             ( l1_pre_topc @ B ) ) =>
% 1.09/1.26           ( ![C:$i]:
% 1.09/1.26             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.09/1.26               ( ![D:$i]:
% 1.09/1.26                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.09/1.26                   ( ![E:$i]:
% 1.09/1.26                     ( ( ( v1_funct_1 @ E ) & 
% 1.09/1.26                         ( v1_funct_2 @
% 1.09/1.26                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.09/1.26                         ( m1_subset_1 @
% 1.09/1.26                           E @ 
% 1.09/1.26                           ( k1_zfmisc_1 @
% 1.09/1.26                             ( k2_zfmisc_1 @
% 1.09/1.26                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.09/1.26                       ( ( ( g1_pre_topc @
% 1.09/1.26                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.09/1.26                           ( D ) ) =>
% 1.09/1.26                         ( ![F:$i]:
% 1.09/1.26                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.09/1.26                             ( ![G:$i]:
% 1.09/1.26                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.09/1.26                                 ( ( ( ( F ) = ( G ) ) & 
% 1.09/1.26                                     ( r1_tmap_1 @
% 1.09/1.26                                       C @ B @ 
% 1.09/1.26                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.09/1.26                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.09/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.26    (~( ![A:$i]:
% 1.09/1.26        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.09/1.26            ( l1_pre_topc @ A ) ) =>
% 1.09/1.26          ( ![B:$i]:
% 1.09/1.26            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.09/1.26                ( l1_pre_topc @ B ) ) =>
% 1.09/1.26              ( ![C:$i]:
% 1.09/1.26                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.09/1.26                  ( ![D:$i]:
% 1.09/1.26                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.09/1.26                      ( ![E:$i]:
% 1.09/1.26                        ( ( ( v1_funct_1 @ E ) & 
% 1.09/1.26                            ( v1_funct_2 @
% 1.09/1.26                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.09/1.26                            ( m1_subset_1 @
% 1.09/1.26                              E @ 
% 1.09/1.26                              ( k1_zfmisc_1 @
% 1.09/1.26                                ( k2_zfmisc_1 @
% 1.09/1.26                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.09/1.26                          ( ( ( g1_pre_topc @
% 1.09/1.26                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.09/1.26                              ( D ) ) =>
% 1.09/1.26                            ( ![F:$i]:
% 1.09/1.26                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.09/1.26                                ( ![G:$i]:
% 1.09/1.26                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.09/1.26                                    ( ( ( ( F ) = ( G ) ) & 
% 1.09/1.26                                        ( r1_tmap_1 @
% 1.09/1.26                                          C @ B @ 
% 1.09/1.26                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.09/1.26                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.09/1.26    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.09/1.26  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('1', plain,
% 1.09/1.26      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.09/1.26        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('2', plain, (((sk_F) = (sk_G))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('3', plain,
% 1.09/1.26      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.09/1.26        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.09/1.26      inference('demod', [status(thm)], ['1', '2'])).
% 1.09/1.26  thf('4', plain,
% 1.09/1.26      ((m1_subset_1 @ sk_E @ 
% 1.09/1.26        (k1_zfmisc_1 @ 
% 1.09/1.26         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(t86_tmap_1, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.26       ( ![B:$i]:
% 1.09/1.26         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.09/1.26             ( l1_pre_topc @ B ) ) =>
% 1.09/1.26           ( ![C:$i]:
% 1.09/1.26             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.09/1.26               ( ![D:$i]:
% 1.09/1.26                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.09/1.26                   ( ![E:$i]:
% 1.09/1.26                     ( ( ( v1_funct_1 @ E ) & 
% 1.09/1.26                         ( v1_funct_2 @
% 1.09/1.26                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.09/1.26                         ( m1_subset_1 @
% 1.09/1.26                           E @ 
% 1.09/1.26                           ( k1_zfmisc_1 @
% 1.09/1.26                             ( k2_zfmisc_1 @
% 1.09/1.26                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.09/1.26                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.09/1.26                         ( ![F:$i]:
% 1.09/1.26                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.09/1.26                             ( ![G:$i]:
% 1.09/1.26                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.09/1.26                                 ( ( ( F ) = ( G ) ) =>
% 1.09/1.26                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.09/1.26                                     ( r1_tmap_1 @
% 1.09/1.26                                       C @ B @ 
% 1.09/1.26                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.09/1.26  thf('5', plain,
% 1.09/1.26      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.09/1.26         ((v2_struct_0 @ X25)
% 1.09/1.26          | ~ (v2_pre_topc @ X25)
% 1.09/1.26          | ~ (l1_pre_topc @ X25)
% 1.09/1.26          | (v2_struct_0 @ X26)
% 1.09/1.26          | ~ (m1_pre_topc @ X26 @ X27)
% 1.09/1.26          | ~ (v1_tsep_1 @ X28 @ X26)
% 1.09/1.26          | ~ (m1_pre_topc @ X28 @ X26)
% 1.09/1.26          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 1.09/1.26          | ((X29) != (X30))
% 1.09/1.26          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.09/1.26               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.09/1.26          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 1.09/1.26          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.09/1.26          | ~ (m1_subset_1 @ X31 @ 
% 1.09/1.26               (k1_zfmisc_1 @ 
% 1.09/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.09/1.26          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.09/1.26          | ~ (v1_funct_1 @ X31)
% 1.09/1.26          | ~ (m1_pre_topc @ X28 @ X27)
% 1.09/1.26          | (v2_struct_0 @ X28)
% 1.09/1.26          | ~ (l1_pre_topc @ X27)
% 1.09/1.26          | ~ (v2_pre_topc @ X27)
% 1.09/1.26          | (v2_struct_0 @ X27))),
% 1.09/1.26      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.09/1.26  thf('6', plain,
% 1.09/1.26      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 1.09/1.26         ((v2_struct_0 @ X27)
% 1.09/1.26          | ~ (v2_pre_topc @ X27)
% 1.09/1.26          | ~ (l1_pre_topc @ X27)
% 1.09/1.26          | (v2_struct_0 @ X28)
% 1.09/1.26          | ~ (m1_pre_topc @ X28 @ X27)
% 1.09/1.26          | ~ (v1_funct_1 @ X31)
% 1.09/1.26          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.09/1.26          | ~ (m1_subset_1 @ X31 @ 
% 1.09/1.26               (k1_zfmisc_1 @ 
% 1.09/1.26                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.09/1.26          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.09/1.26          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 1.09/1.26          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.09/1.26               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.09/1.26          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 1.09/1.26          | ~ (m1_pre_topc @ X28 @ X26)
% 1.09/1.26          | ~ (v1_tsep_1 @ X28 @ X26)
% 1.09/1.26          | ~ (m1_pre_topc @ X26 @ X27)
% 1.09/1.26          | (v2_struct_0 @ X26)
% 1.09/1.26          | ~ (l1_pre_topc @ X25)
% 1.09/1.26          | ~ (v2_pre_topc @ X25)
% 1.09/1.26          | (v2_struct_0 @ X25))),
% 1.09/1.26      inference('simplify', [status(thm)], ['5'])).
% 1.09/1.26  thf('7', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         ((v2_struct_0 @ sk_B)
% 1.09/1.26          | ~ (v2_pre_topc @ sk_B)
% 1.09/1.26          | ~ (l1_pre_topc @ sk_B)
% 1.09/1.26          | (v2_struct_0 @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.09/1.26          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.09/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.09/1.26          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.09/1.26               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.09/1.26          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.09/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.09/1.26          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.09/1.26          | ~ (v1_funct_1 @ sk_E)
% 1.09/1.26          | ~ (m1_pre_topc @ X1 @ X0)
% 1.09/1.26          | (v2_struct_0 @ X1)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | ~ (v2_pre_topc @ X0)
% 1.09/1.26          | (v2_struct_0 @ X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['4', '6'])).
% 1.09/1.26  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('10', plain,
% 1.09/1.26      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('12', plain,
% 1.09/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.26         ((v2_struct_0 @ sk_B)
% 1.09/1.26          | (v2_struct_0 @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.09/1.26          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.09/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.09/1.26          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.09/1.26               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.09/1.26          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.09/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.09/1.26          | ~ (m1_pre_topc @ X1 @ X0)
% 1.09/1.26          | (v2_struct_0 @ X1)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | ~ (v2_pre_topc @ X0)
% 1.09/1.26          | (v2_struct_0 @ X0))),
% 1.09/1.26      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.09/1.26  thf('13', plain,
% 1.09/1.26      (((v2_struct_0 @ sk_A)
% 1.09/1.26        | ~ (v2_pre_topc @ sk_A)
% 1.09/1.26        | ~ (l1_pre_topc @ sk_A)
% 1.09/1.26        | (v2_struct_0 @ sk_C)
% 1.09/1.26        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.09/1.26        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.09/1.26        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.09/1.26        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.09/1.26        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.09/1.26        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.09/1.26        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.09/1.26        | (v2_struct_0 @ sk_D)
% 1.09/1.26        | (v2_struct_0 @ sk_B))),
% 1.09/1.26      inference('sup-', [status(thm)], ['3', '12'])).
% 1.09/1.26  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('18', plain, (((sk_F) = (sk_G))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.09/1.26      inference('demod', [status(thm)], ['17', '18'])).
% 1.09/1.26  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('21', plain,
% 1.09/1.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(t2_tsep_1, axiom,
% 1.09/1.26    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.09/1.26  thf('22', plain,
% 1.09/1.26      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.09/1.26      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.09/1.26  thf(t65_pre_topc, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( l1_pre_topc @ A ) =>
% 1.09/1.26       ( ![B:$i]:
% 1.09/1.26         ( ( l1_pre_topc @ B ) =>
% 1.09/1.26           ( ( m1_pre_topc @ A @ B ) <=>
% 1.09/1.26             ( m1_pre_topc @
% 1.09/1.26               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.09/1.26  thf('23', plain,
% 1.09/1.26      (![X6 : $i, X7 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ X6)
% 1.09/1.26          | ~ (m1_pre_topc @ X7 @ X6)
% 1.09/1.26          | (m1_pre_topc @ X7 @ 
% 1.09/1.26             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.09/1.26          | ~ (l1_pre_topc @ X7))),
% 1.09/1.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.09/1.26  thf('24', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ X0)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | (m1_pre_topc @ X0 @ 
% 1.09/1.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.09/1.26          | ~ (l1_pre_topc @ X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['22', '23'])).
% 1.09/1.26  thf('25', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         ((m1_pre_topc @ X0 @ 
% 1.09/1.26           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.09/1.26          | ~ (l1_pre_topc @ X0))),
% 1.09/1.26      inference('simplify', [status(thm)], ['24'])).
% 1.09/1.26  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 1.09/1.26      inference('sup+', [status(thm)], ['21', '25'])).
% 1.09/1.26  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf(dt_m1_pre_topc, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( l1_pre_topc @ A ) =>
% 1.09/1.26       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.09/1.26  thf('28', plain,
% 1.09/1.26      (![X4 : $i, X5 : $i]:
% 1.09/1.26         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.09/1.26      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.09/1.26  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.09/1.26      inference('sup-', [status(thm)], ['27', '28'])).
% 1.09/1.26  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.26  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.09/1.26      inference('demod', [status(thm)], ['26', '31'])).
% 1.09/1.26  thf('33', plain,
% 1.09/1.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('34', plain,
% 1.09/1.26      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.09/1.26      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.09/1.26  thf('35', plain,
% 1.09/1.26      (![X6 : $i, X7 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ X6)
% 1.09/1.26          | ~ (m1_pre_topc @ X7 @ 
% 1.09/1.26               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.09/1.26          | (m1_pre_topc @ X7 @ X6)
% 1.09/1.26          | ~ (l1_pre_topc @ X7))),
% 1.09/1.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.09/1.26  thf('36', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ 
% 1.09/1.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.09/1.26          | ~ (l1_pre_topc @ 
% 1.09/1.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.09/1.26          | (m1_pre_topc @ 
% 1.09/1.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.09/1.26          | ~ (l1_pre_topc @ X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['34', '35'])).
% 1.09/1.26  thf('37', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ X0)
% 1.09/1.26          | (m1_pre_topc @ 
% 1.09/1.26             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.09/1.26          | ~ (l1_pre_topc @ 
% 1.09/1.26               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.09/1.26      inference('simplify', [status(thm)], ['36'])).
% 1.09/1.26  thf('38', plain,
% 1.09/1.26      ((~ (l1_pre_topc @ sk_D)
% 1.09/1.26        | (m1_pre_topc @ 
% 1.09/1.26           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 1.09/1.26        | ~ (l1_pre_topc @ sk_C))),
% 1.09/1.26      inference('sup-', [status(thm)], ['33', '37'])).
% 1.09/1.26  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('40', plain,
% 1.09/1.26      (![X4 : $i, X5 : $i]:
% 1.09/1.26         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.09/1.26      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.09/1.26  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.09/1.26      inference('sup-', [status(thm)], ['39', '40'])).
% 1.09/1.26  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('43', plain, ((l1_pre_topc @ sk_D)),
% 1.09/1.26      inference('demod', [status(thm)], ['41', '42'])).
% 1.09/1.26  thf('44', plain,
% 1.09/1.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.26  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['38', '43', '44', '45'])).
% 1.09/1.26  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.09/1.26      inference('demod', [status(thm)], ['26', '31'])).
% 1.09/1.26  thf(t35_borsuk_1, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( l1_pre_topc @ A ) =>
% 1.09/1.26       ( ![B:$i]:
% 1.09/1.26         ( ( m1_pre_topc @ B @ A ) =>
% 1.09/1.26           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.09/1.26  thf('48', plain,
% 1.09/1.26      (![X20 : $i, X21 : $i]:
% 1.09/1.26         (~ (m1_pre_topc @ X20 @ X21)
% 1.09/1.26          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 1.09/1.26          | ~ (l1_pre_topc @ X21))),
% 1.09/1.26      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.09/1.26  thf('49', plain,
% 1.09/1.26      ((~ (l1_pre_topc @ sk_D)
% 1.09/1.26        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 1.09/1.26      inference('sup-', [status(thm)], ['47', '48'])).
% 1.09/1.26  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 1.09/1.26      inference('demod', [status(thm)], ['41', '42'])).
% 1.09/1.26  thf('51', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 1.09/1.26      inference('demod', [status(thm)], ['49', '50'])).
% 1.09/1.26  thf(t19_tsep_1, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.26       ( ![B:$i]:
% 1.09/1.26         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.09/1.26           ( ![C:$i]:
% 1.09/1.26             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.09/1.26               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 1.09/1.26                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 1.09/1.26  thf('52', plain,
% 1.09/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.09/1.26         (~ (v1_tsep_1 @ X14 @ X15)
% 1.09/1.26          | ~ (m1_pre_topc @ X14 @ X15)
% 1.09/1.26          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 1.09/1.26          | (v1_tsep_1 @ X14 @ X16)
% 1.09/1.26          | ~ (m1_pre_topc @ X16 @ X15)
% 1.09/1.26          | (v2_struct_0 @ X16)
% 1.09/1.26          | ~ (l1_pre_topc @ X15)
% 1.09/1.26          | ~ (v2_pre_topc @ X15)
% 1.09/1.26          | (v2_struct_0 @ X15))),
% 1.09/1.26      inference('cnf', [status(esa)], [t19_tsep_1])).
% 1.09/1.26  thf('53', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         ((v2_struct_0 @ X0)
% 1.09/1.26          | ~ (v2_pre_topc @ X0)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | (v2_struct_0 @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.09/1.26          | (v1_tsep_1 @ sk_C @ sk_D)
% 1.09/1.26          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.09/1.26          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 1.09/1.26      inference('sup-', [status(thm)], ['51', '52'])).
% 1.09/1.26  thf('54', plain,
% 1.09/1.26      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 1.09/1.26        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.09/1.26        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.09/1.26        | (v2_struct_0 @ sk_D)
% 1.09/1.26        | ~ (l1_pre_topc @ sk_C)
% 1.09/1.26        | ~ (v2_pre_topc @ sk_C)
% 1.09/1.26        | (v2_struct_0 @ sk_C))),
% 1.09/1.26      inference('sup-', [status(thm)], ['46', '53'])).
% 1.09/1.26  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.09/1.26      inference('demod', [status(thm)], ['26', '31'])).
% 1.09/1.26  thf('56', plain,
% 1.09/1.26      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.09/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.26  thf('57', plain,
% 1.09/1.26      (![X6 : $i, X7 : $i]:
% 1.09/1.26         (~ (l1_pre_topc @ X6)
% 1.09/1.26          | ~ (m1_pre_topc @ X7 @ 
% 1.09/1.26               (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 1.09/1.26          | (m1_pre_topc @ X7 @ X6)
% 1.09/1.26          | ~ (l1_pre_topc @ X7))),
% 1.09/1.26      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.09/1.26  thf('58', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | (m1_pre_topc @ X0 @ sk_C)
% 1.09/1.26          | ~ (l1_pre_topc @ sk_C))),
% 1.09/1.26      inference('sup-', [status(thm)], ['56', '57'])).
% 1.09/1.26  thf('59', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.26  thf('60', plain,
% 1.09/1.26      (![X0 : $i]:
% 1.09/1.26         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.09/1.26          | ~ (l1_pre_topc @ X0)
% 1.09/1.26          | (m1_pre_topc @ X0 @ sk_C))),
% 1.09/1.26      inference('demod', [status(thm)], ['58', '59'])).
% 1.09/1.26  thf('61', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.09/1.26      inference('sup-', [status(thm)], ['55', '60'])).
% 1.09/1.26  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.26  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.09/1.26      inference('demod', [status(thm)], ['61', '62'])).
% 1.09/1.26  thf(fc10_tops_1, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.26       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.09/1.26  thf('64', plain,
% 1.09/1.26      (![X8 : $i]:
% 1.09/1.26         ((v3_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 1.09/1.26          | ~ (l1_pre_topc @ X8)
% 1.09/1.26          | ~ (v2_pre_topc @ X8))),
% 1.09/1.26      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.09/1.26  thf(d3_struct_0, axiom,
% 1.09/1.26    (![A:$i]:
% 1.09/1.26     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.09/1.27  thf('65', plain,
% 1.09/1.27      (![X2 : $i]:
% 1.09/1.27         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 1.09/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.09/1.27  thf('66', plain,
% 1.09/1.27      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.09/1.27      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.09/1.27  thf(t1_tsep_1, axiom,
% 1.09/1.27    (![A:$i]:
% 1.09/1.27     ( ( l1_pre_topc @ A ) =>
% 1.09/1.27       ( ![B:$i]:
% 1.09/1.27         ( ( m1_pre_topc @ B @ A ) =>
% 1.09/1.27           ( m1_subset_1 @
% 1.09/1.27             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.09/1.27  thf('67', plain,
% 1.09/1.27      (![X17 : $i, X18 : $i]:
% 1.09/1.27         (~ (m1_pre_topc @ X17 @ X18)
% 1.09/1.27          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 1.09/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.09/1.27          | ~ (l1_pre_topc @ X18))),
% 1.09/1.27      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.09/1.27  thf('68', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.09/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.09/1.27      inference('sup-', [status(thm)], ['66', '67'])).
% 1.09/1.27  thf('69', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.09/1.27           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.09/1.27          | ~ (l1_pre_topc @ X0))),
% 1.09/1.27      inference('simplify', [status(thm)], ['68'])).
% 1.09/1.27  thf(t16_tsep_1, axiom,
% 1.09/1.27    (![A:$i]:
% 1.09/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.27       ( ![B:$i]:
% 1.09/1.27         ( ( m1_pre_topc @ B @ A ) =>
% 1.09/1.27           ( ![C:$i]:
% 1.09/1.27             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.27               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.09/1.27                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.09/1.27                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.09/1.27  thf('70', plain,
% 1.09/1.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.09/1.27         (~ (m1_pre_topc @ X11 @ X12)
% 1.09/1.27          | ((X13) != (u1_struct_0 @ X11))
% 1.09/1.27          | ~ (v3_pre_topc @ X13 @ X12)
% 1.09/1.27          | (v1_tsep_1 @ X11 @ X12)
% 1.09/1.27          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.09/1.27          | ~ (l1_pre_topc @ X12)
% 1.09/1.27          | ~ (v2_pre_topc @ X12))),
% 1.09/1.27      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.09/1.27  thf('71', plain,
% 1.09/1.27      (![X11 : $i, X12 : $i]:
% 1.09/1.27         (~ (v2_pre_topc @ X12)
% 1.09/1.27          | ~ (l1_pre_topc @ X12)
% 1.09/1.27          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 1.09/1.27               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.09/1.27          | (v1_tsep_1 @ X11 @ X12)
% 1.09/1.27          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 1.09/1.27          | ~ (m1_pre_topc @ X11 @ X12))),
% 1.09/1.27      inference('simplify', [status(thm)], ['70'])).
% 1.09/1.27  thf('72', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (m1_pre_topc @ X0 @ X0)
% 1.09/1.27          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.09/1.27          | (v1_tsep_1 @ X0 @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (v2_pre_topc @ X0))),
% 1.09/1.27      inference('sup-', [status(thm)], ['69', '71'])).
% 1.09/1.27  thf('73', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (v2_pre_topc @ X0)
% 1.09/1.27          | (v1_tsep_1 @ X0 @ X0)
% 1.09/1.27          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.09/1.27          | ~ (m1_pre_topc @ X0 @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0))),
% 1.09/1.27      inference('simplify', [status(thm)], ['72'])).
% 1.09/1.27  thf('74', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.09/1.27          | ~ (l1_struct_0 @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (m1_pre_topc @ X0 @ X0)
% 1.09/1.27          | (v1_tsep_1 @ X0 @ X0)
% 1.09/1.27          | ~ (v2_pre_topc @ X0))),
% 1.09/1.27      inference('sup-', [status(thm)], ['65', '73'])).
% 1.09/1.27  thf('75', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (v2_pre_topc @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (v2_pre_topc @ X0)
% 1.09/1.27          | (v1_tsep_1 @ X0 @ X0)
% 1.09/1.27          | ~ (m1_pre_topc @ X0 @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (l1_struct_0 @ X0))),
% 1.09/1.27      inference('sup-', [status(thm)], ['64', '74'])).
% 1.09/1.27  thf('76', plain,
% 1.09/1.27      (![X0 : $i]:
% 1.09/1.27         (~ (l1_struct_0 @ X0)
% 1.09/1.27          | ~ (m1_pre_topc @ X0 @ X0)
% 1.09/1.27          | (v1_tsep_1 @ X0 @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X0)
% 1.09/1.27          | ~ (v2_pre_topc @ X0))),
% 1.09/1.27      inference('simplify', [status(thm)], ['75'])).
% 1.09/1.27  thf('77', plain,
% 1.09/1.27      ((~ (v2_pre_topc @ sk_C)
% 1.09/1.27        | ~ (l1_pre_topc @ sk_C)
% 1.09/1.27        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.09/1.27        | ~ (l1_struct_0 @ sk_C))),
% 1.09/1.27      inference('sup-', [status(thm)], ['63', '76'])).
% 1.09/1.27  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf(cc1_pre_topc, axiom,
% 1.09/1.27    (![A:$i]:
% 1.09/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.27       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.09/1.27  thf('79', plain,
% 1.09/1.27      (![X0 : $i, X1 : $i]:
% 1.09/1.27         (~ (m1_pre_topc @ X0 @ X1)
% 1.09/1.27          | (v2_pre_topc @ X0)
% 1.09/1.27          | ~ (l1_pre_topc @ X1)
% 1.09/1.27          | ~ (v2_pre_topc @ X1))),
% 1.09/1.27      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.09/1.27  thf('80', plain,
% 1.09/1.27      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.09/1.27      inference('sup-', [status(thm)], ['78', '79'])).
% 1.09/1.27  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('83', plain, ((v2_pre_topc @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.09/1.27  thf('84', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.27  thf('85', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.27  thf(dt_l1_pre_topc, axiom,
% 1.09/1.27    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.09/1.27  thf('86', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.09/1.27      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.09/1.27  thf('87', plain, ((l1_struct_0 @ sk_C)),
% 1.09/1.27      inference('sup-', [status(thm)], ['85', '86'])).
% 1.09/1.27  thf('88', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['77', '83', '84', '87'])).
% 1.09/1.27  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['61', '62'])).
% 1.09/1.27  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['29', '30'])).
% 1.09/1.27  thf('91', plain, ((v2_pre_topc @ sk_C)),
% 1.09/1.27      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.09/1.27  thf('92', plain,
% 1.09/1.27      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.09/1.27      inference('demod', [status(thm)], ['54', '88', '89', '90', '91'])).
% 1.09/1.27  thf('93', plain, (~ (v2_struct_0 @ sk_D)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('94', plain, (((v2_struct_0 @ sk_C) | (v1_tsep_1 @ sk_C @ sk_D))),
% 1.09/1.27      inference('clc', [status(thm)], ['92', '93'])).
% 1.09/1.27  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('96', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.09/1.27      inference('clc', [status(thm)], ['94', '95'])).
% 1.09/1.27  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('98', plain,
% 1.09/1.27      (((v2_struct_0 @ sk_A)
% 1.09/1.27        | (v2_struct_0 @ sk_C)
% 1.09/1.27        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.09/1.27        | (v2_struct_0 @ sk_D)
% 1.09/1.27        | (v2_struct_0 @ sk_B))),
% 1.09/1.27      inference('demod', [status(thm)],
% 1.09/1.27                ['13', '14', '15', '16', '19', '20', '32', '96', '97'])).
% 1.09/1.27  thf('99', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('100', plain,
% 1.09/1.27      (((v2_struct_0 @ sk_B)
% 1.09/1.27        | (v2_struct_0 @ sk_D)
% 1.09/1.27        | (v2_struct_0 @ sk_C)
% 1.09/1.27        | (v2_struct_0 @ sk_A))),
% 1.09/1.27      inference('sup-', [status(thm)], ['98', '99'])).
% 1.09/1.27  thf('101', plain, (~ (v2_struct_0 @ sk_D)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('102', plain,
% 1.09/1.27      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 1.09/1.27      inference('sup-', [status(thm)], ['100', '101'])).
% 1.09/1.27  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('104', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.09/1.27      inference('clc', [status(thm)], ['102', '103'])).
% 1.09/1.27  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 1.09/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.27  thf('106', plain, ((v2_struct_0 @ sk_C)),
% 1.09/1.27      inference('clc', [status(thm)], ['104', '105'])).
% 1.09/1.27  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 1.09/1.27  
% 1.09/1.27  % SZS output end Refutation
% 1.09/1.27  
% 1.09/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
