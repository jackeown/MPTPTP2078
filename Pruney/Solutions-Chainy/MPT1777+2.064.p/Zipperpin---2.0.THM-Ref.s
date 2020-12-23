%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R8evfFFPau

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:36 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 279 expanded)
%              Number of leaves         :   39 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          : 1214 (7911 expanded)
%              Number of equality atoms :   18 ( 202 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_tsep_1 @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ( X27 != X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( v1_tsep_1 @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('34',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('47',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','50','51','54'])).

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

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_tsep_1 @ X14 @ X15 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('60',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('62',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('72',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('73',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('81',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['58','59','73','78','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','85','86'])).

thf('88',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R8evfFFPau
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 459 iterations in 0.233s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.65  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.65  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.65  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.47/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.65  thf(t88_tmap_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65             ( l1_pre_topc @ B ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ![E:$i]:
% 0.47/0.65                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                         ( v1_funct_2 @
% 0.47/0.65                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                         ( m1_subset_1 @
% 0.47/0.65                           E @ 
% 0.47/0.65                           ( k1_zfmisc_1 @
% 0.47/0.65                             ( k2_zfmisc_1 @
% 0.47/0.65                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                       ( ( ( g1_pre_topc @
% 0.47/0.65                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.65                           ( D ) ) =>
% 0.47/0.65                         ( ![F:$i]:
% 0.47/0.65                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                             ( ![G:$i]:
% 0.47/0.65                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                 ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.65                                     ( r1_tmap_1 @
% 0.47/0.65                                       C @ B @ 
% 0.47/0.65                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.65                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65            ( l1_pre_topc @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65                ( l1_pre_topc @ B ) ) =>
% 0.47/0.65              ( ![C:$i]:
% 0.47/0.65                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65                  ( ![D:$i]:
% 0.47/0.65                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                      ( ![E:$i]:
% 0.47/0.65                        ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                            ( v1_funct_2 @
% 0.47/0.65                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                            ( m1_subset_1 @
% 0.47/0.65                              E @ 
% 0.47/0.65                              ( k1_zfmisc_1 @
% 0.47/0.65                                ( k2_zfmisc_1 @
% 0.47/0.65                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                          ( ( ( g1_pre_topc @
% 0.47/0.65                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.65                              ( D ) ) =>
% 0.47/0.65                            ( ![F:$i]:
% 0.47/0.65                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                                ( ![G:$i]:
% 0.47/0.65                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                    ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.65                                        ( r1_tmap_1 @
% 0.47/0.65                                          C @ B @ 
% 0.47/0.65                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.65                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.47/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.65        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('2', plain, (((sk_F) = (sk_G))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.65        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.47/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_E @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t86_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65             ( l1_pre_topc @ B ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ![E:$i]:
% 0.47/0.65                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                         ( v1_funct_2 @
% 0.47/0.65                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                         ( m1_subset_1 @
% 0.47/0.65                           E @ 
% 0.47/0.65                           ( k1_zfmisc_1 @
% 0.47/0.65                             ( k2_zfmisc_1 @
% 0.47/0.65                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.47/0.65                         ( ![F:$i]:
% 0.47/0.65                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                             ( ![G:$i]:
% 0.47/0.65                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                 ( ( ( F ) = ( G ) ) =>
% 0.47/0.65                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.47/0.65                                     ( r1_tmap_1 @
% 0.47/0.65                                       C @ B @ 
% 0.47/0.65                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X23)
% 0.47/0.65          | ~ (v2_pre_topc @ X23)
% 0.47/0.65          | ~ (l1_pre_topc @ X23)
% 0.47/0.65          | (v2_struct_0 @ X24)
% 0.47/0.65          | ~ (m1_pre_topc @ X24 @ X25)
% 0.47/0.65          | ~ (v1_tsep_1 @ X26 @ X24)
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X24)
% 0.47/0.65          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.47/0.65          | ((X27) != (X28))
% 0.47/0.65          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.47/0.65               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.47/0.65          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X27)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (m1_subset_1 @ X29 @ 
% 0.47/0.65               (k1_zfmisc_1 @ 
% 0.47/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.47/0.65          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.47/0.65          | ~ (v1_funct_1 @ X29)
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X25)
% 0.47/0.65          | (v2_struct_0 @ X26)
% 0.47/0.65          | ~ (l1_pre_topc @ X25)
% 0.47/0.65          | ~ (v2_pre_topc @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X25)
% 0.47/0.65          | ~ (v2_pre_topc @ X25)
% 0.47/0.65          | ~ (l1_pre_topc @ X25)
% 0.47/0.65          | (v2_struct_0 @ X26)
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X25)
% 0.47/0.65          | ~ (v1_funct_1 @ X29)
% 0.47/0.65          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.47/0.65          | ~ (m1_subset_1 @ X29 @ 
% 0.47/0.65               (k1_zfmisc_1 @ 
% 0.47/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.47/0.65          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X28)
% 0.47/0.65          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.47/0.65               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X24)
% 0.47/0.65          | ~ (v1_tsep_1 @ X26 @ X24)
% 0.47/0.65          | ~ (m1_pre_topc @ X24 @ X25)
% 0.47/0.65          | (v2_struct_0 @ X24)
% 0.47/0.65          | ~ (l1_pre_topc @ X23)
% 0.47/0.65          | ~ (v2_pre_topc @ X23)
% 0.47/0.65          | (v2_struct_0 @ X23))),
% 0.47/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_B)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.65          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.65          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.47/0.65          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.65               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.47/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '6'])).
% 0.47/0.65  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_B)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.65          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.47/0.65          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.65               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.65        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.47/0.65        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.47/0.65        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.65        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.47/0.65        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['3', '12'])).
% 0.47/0.65  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('18', plain, (((sk_F) = (sk_G))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t2_tsep_1, axiom,
% 0.47/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.65  thf(t65_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( l1_pre_topc @ B ) =>
% 0.47/0.65           ( ( m1_pre_topc @ A @ B ) <=>
% 0.47/0.65             ( m1_pre_topc @
% 0.47/0.65               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X11)
% 0.47/0.65          | ~ (m1_pre_topc @ X12 @ X11)
% 0.47/0.65          | (m1_pre_topc @ X12 @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.47/0.65          | ~ (l1_pre_topc @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (m1_pre_topc @ X0 @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_pre_topc @ X0 @ 
% 0.47/0.65           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.65  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['21', '25'])).
% 0.47/0.65  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_m1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['26', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(fc10_tops_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      (![X13 : $i]:
% 0.47/0.65         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.47/0.65          | ~ (l1_pre_topc @ X13)
% 0.47/0.65          | ~ (v2_pre_topc @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.65  thf(d3_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf(dt_k2_subset_1, axiom,
% 0.47/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.47/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.65  thf('37', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.65  thf('38', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf(t60_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.47/0.65             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.47/0.65           ( ( v3_pre_topc @
% 0.47/0.65               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.65             ( m1_subset_1 @
% 0.47/0.65               B @ 
% 0.47/0.65               ( k1_zfmisc_1 @
% 0.47/0.65                 ( u1_struct_0 @
% 0.47/0.65                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X9 : $i, X10 : $i]:
% 0.47/0.65         (~ (v3_pre_topc @ X10 @ X9)
% 0.47/0.65          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.47/0.65          | (m1_subset_1 @ X10 @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (u1_struct_0 @ 
% 0.47/0.65               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))))
% 0.47/0.65          | ~ (l1_pre_topc @ X9)
% 0.47/0.65          | ~ (v2_pre_topc @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (u1_struct_0 @ 
% 0.47/0.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.65          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (u1_struct_0 @ 
% 0.47/0.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['35', '40'])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (u1_struct_0 @ 
% 0.47/0.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.65          | ~ (l1_struct_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['34', '41'])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (u1_struct_0 @ 
% 0.47/0.65               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.47/0.65        | ~ (v2_pre_topc @ sk_C)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.65        | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['33', '43'])).
% 0.47/0.65  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X2 @ X3)
% 0.47/0.65          | (v2_pre_topc @ X2)
% 0.47/0.65          | ~ (l1_pre_topc @ X3)
% 0.47/0.65          | ~ (v2_pre_topc @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('50', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.47/0.65  thf('51', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('52', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf(dt_l1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.65  thf('53', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('54', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.47/0.65      inference('demod', [status(thm)], ['44', '50', '51', '54'])).
% 0.47/0.65  thf(t16_tsep_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.47/0.65                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.65                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X14 @ X15)
% 0.47/0.65          | ((X16) != (u1_struct_0 @ X14))
% 0.47/0.65          | ~ (v3_pre_topc @ X16 @ X15)
% 0.47/0.65          | (v1_tsep_1 @ X14 @ X15)
% 0.47/0.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.65          | ~ (l1_pre_topc @ X15)
% 0.47/0.65          | ~ (v2_pre_topc @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i]:
% 0.47/0.65         (~ (v2_pre_topc @ X15)
% 0.47/0.65          | ~ (l1_pre_topc @ X15)
% 0.47/0.65          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.47/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.47/0.65          | (v1_tsep_1 @ X14 @ X15)
% 0.47/0.65          | ~ (v3_pre_topc @ (u1_struct_0 @ X14) @ X15)
% 0.47/0.65          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.47/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.47/0.65        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['55', '57'])).
% 0.47/0.65  thf('59', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['26', '31'])).
% 0.47/0.65  thf('60', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      (![X13 : $i]:
% 0.47/0.65         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.47/0.65          | ~ (l1_pre_topc @ X13)
% 0.47/0.65          | ~ (v2_pre_topc @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('63', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.47/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X9 : $i, X10 : $i]:
% 0.47/0.65         (~ (v3_pre_topc @ X10 @ X9)
% 0.47/0.65          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.47/0.65          | (v3_pre_topc @ X10 @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.47/0.65          | ~ (l1_pre_topc @ X9)
% 0.47/0.65          | ~ (v2_pre_topc @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['62', '65'])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (l1_struct_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['61', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X0)
% 0.47/0.65          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['67'])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_C)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.65        | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['60', '68'])).
% 0.47/0.65  thf('70', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.47/0.65  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('72', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('73', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.47/0.65  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('76', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.65  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('78', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['76', '77'])).
% 0.47/0.65  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X2 @ X3)
% 0.47/0.65          | (v2_pre_topc @ X2)
% 0.47/0.65          | ~ (l1_pre_topc @ X3)
% 0.47/0.65          | ~ (v2_pre_topc @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['79', '80'])).
% 0.47/0.65  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('84', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.47/0.65  thf('85', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['58', '59', '73', '78', '84'])).
% 0.47/0.65  thf('86', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['13', '14', '15', '16', '19', '20', '32', '85', '86'])).
% 0.47/0.65  thf('88', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_B)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.65  thf('90', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.65  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('93', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['91', '92'])).
% 0.47/0.65  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('95', plain, ((v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('clc', [status(thm)], ['93', '94'])).
% 0.47/0.65  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
