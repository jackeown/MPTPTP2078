%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gPkt4Rq1Tq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 277 expanded)
%              Number of leaves         :   37 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          : 1252 (8418 expanded)
%              Number of equality atoms :   19 ( 215 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_tsep_1 @ X24 @ X22 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( X25 != X26 )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( v1_tsep_1 @ X24 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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

thf('33',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('34',plain,(
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

thf('35',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

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

thf('40',plain,(
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

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('50',plain,
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

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( X10
       != ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v1_tsep_1 @ X9 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t14_tmap_1])).

thf('52',plain,(
    ! [X9: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( v1_tsep_1 @ X9 @ X11 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) @ X11 )
      | ~ ( v1_tsep_1 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) @ X11 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
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
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('62',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('67',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tsep_1 @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['53','59','65','66','67','68','69','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['49','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('78',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('79',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('80',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['48','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('83',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('84',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('85',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['81','82','83','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','87','88'])).

thf('90',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gPkt4Rq1Tq
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 292 iterations in 0.149s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
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
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.61            ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61                ( l1_pre_topc @ B ) ) =>
% 0.41/0.61              ( ![C:$i]:
% 0.41/0.61                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.61                  ( ![D:$i]:
% 0.41/0.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.61                      ( ![E:$i]:
% 0.41/0.61                        ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.61                            ( v1_funct_2 @
% 0.41/0.61                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                            ( m1_subset_1 @
% 0.41/0.61                              E @ 
% 0.41/0.61                              ( k1_zfmisc_1 @
% 0.41/0.61                                ( k2_zfmisc_1 @
% 0.41/0.61                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61                          ( ( ( g1_pre_topc @
% 0.41/0.61                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.41/0.61                              ( D ) ) =>
% 0.41/0.61                            ( ![F:$i]:
% 0.41/0.61                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.61                                ( ![G:$i]:
% 0.41/0.61                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.61                                    ( ( ( ( F ) = ( G ) ) & 
% 0.41/0.61                                        ( r1_tmap_1 @
% 0.41/0.61                                          C @ B @ 
% 0.41/0.61                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.41/0.61                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.41/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.61        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('2', plain, (((sk_F) = (sk_G))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.61        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.41/0.61      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_E @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t86_tmap_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.61                   ( ![E:$i]:
% 0.41/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.61                         ( v1_funct_2 @
% 0.41/0.61                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                         ( m1_subset_1 @
% 0.41/0.61                           E @ 
% 0.41/0.61                           ( k1_zfmisc_1 @
% 0.41/0.61                             ( k2_zfmisc_1 @
% 0.41/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.41/0.61                         ( ![F:$i]:
% 0.41/0.61                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.61                             ( ![G:$i]:
% 0.41/0.61                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.61                                 ( ( ( F ) = ( G ) ) =>
% 0.41/0.61                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.41/0.61                                     ( r1_tmap_1 @
% 0.41/0.61                                       C @ B @ 
% 0.41/0.61                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X21)
% 0.41/0.61          | ~ (v2_pre_topc @ X21)
% 0.41/0.61          | ~ (l1_pre_topc @ X21)
% 0.41/0.61          | (v2_struct_0 @ X22)
% 0.41/0.61          | ~ (m1_pre_topc @ X22 @ X23)
% 0.41/0.61          | ~ (v1_tsep_1 @ X24 @ X22)
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X22)
% 0.41/0.61          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.41/0.61          | ((X25) != (X26))
% 0.41/0.61          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.41/0.61               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.41/0.61          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X25)
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.41/0.61          | ~ (m1_subset_1 @ X27 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.41/0.61          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.41/0.61          | ~ (v1_funct_1 @ X27)
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X23)
% 0.41/0.61          | (v2_struct_0 @ X24)
% 0.41/0.61          | ~ (l1_pre_topc @ X23)
% 0.41/0.61          | ~ (v2_pre_topc @ X23)
% 0.41/0.61          | (v2_struct_0 @ X23))),
% 0.41/0.61      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X26 : $i, X27 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X23)
% 0.41/0.61          | ~ (v2_pre_topc @ X23)
% 0.41/0.61          | ~ (l1_pre_topc @ X23)
% 0.41/0.61          | (v2_struct_0 @ X24)
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X23)
% 0.41/0.61          | ~ (v1_funct_1 @ X27)
% 0.41/0.61          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.41/0.61          | ~ (m1_subset_1 @ X27 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.41/0.61          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X26)
% 0.41/0.61          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.41/0.61               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X22))
% 0.41/0.61          | ~ (m1_pre_topc @ X24 @ X22)
% 0.41/0.61          | ~ (v1_tsep_1 @ X24 @ X22)
% 0.41/0.61          | ~ (m1_pre_topc @ X22 @ X23)
% 0.41/0.61          | (v2_struct_0 @ X22)
% 0.41/0.61          | ~ (l1_pre_topc @ X21)
% 0.41/0.61          | ~ (v2_pre_topc @ X21)
% 0.41/0.61          | (v2_struct_0 @ X21))),
% 0.41/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.41/0.61          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.41/0.61               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.41/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.41/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X1)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '6'])).
% 0.41/0.61  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.41/0.61          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.41/0.61               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.41/0.61          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X1)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_C)
% 0.41/0.61        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.41/0.61        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.41/0.61        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.61        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.41/0.61        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.41/0.61        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.41/0.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '12'])).
% 0.41/0.61  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('18', plain, (((sk_F) = (sk_G))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t2_tsep_1, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf(t65_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( l1_pre_topc @ B ) =>
% 0.41/0.61           ( ( m1_pre_topc @ A @ B ) <=>
% 0.41/0.61             ( m1_pre_topc @
% 0.41/0.61               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X6)
% 0.41/0.61          | ~ (m1_pre_topc @ X7 @ X6)
% 0.41/0.61          | (m1_pre_topc @ X7 @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.41/0.61          | ~ (l1_pre_topc @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (m1_pre_topc @ X0 @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_pre_topc @ X0 @ 
% 0.41/0.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.41/0.61  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.41/0.61      inference('sup+', [status(thm)], ['21', '25'])).
% 0.41/0.61  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_m1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.61  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf(fc10_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X8 : $i]:
% 0.41/0.61         ((v3_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 0.41/0.61          | ~ (l1_pre_topc @ X8)
% 0.41/0.61          | ~ (v2_pre_topc @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.41/0.61  thf(d3_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X2 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf(t1_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( m1_subset_1 @
% 0.41/0.61             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X15 @ X16)
% 0.41/0.61          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61          | ~ (l1_pre_topc @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.61  thf(t16_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.61                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.61                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X12 @ X13)
% 0.41/0.61          | ((X14) != (u1_struct_0 @ X12))
% 0.41/0.61          | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61          | (v1_tsep_1 @ X12 @ X13)
% 0.41/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61          | ~ (l1_pre_topc @ X13)
% 0.41/0.61          | ~ (v2_pre_topc @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X13)
% 0.41/0.61          | ~ (l1_pre_topc @ X13)
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61          | (v1_tsep_1 @ X12 @ X13)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.41/0.61          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.41/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['34', '44'])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '46'])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t14_tmap_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.41/0.61               ( ( ( C ) =
% 0.41/0.61                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.41/0.61                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.61                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X9)
% 0.41/0.61          | ~ (l1_pre_topc @ X9)
% 0.41/0.61          | ((X10) != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.41/0.61          | ~ (v1_tsep_1 @ X10 @ X11)
% 0.41/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.41/0.61          | (v1_tsep_1 @ X9 @ X11)
% 0.41/0.61          | ~ (l1_pre_topc @ X10)
% 0.41/0.61          | ~ (v2_pre_topc @ X10)
% 0.41/0.61          | ~ (l1_pre_topc @ X11)
% 0.41/0.61          | ~ (v2_pre_topc @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [t14_tmap_1])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      (![X9 : $i, X11 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X11)
% 0.41/0.61          | ~ (l1_pre_topc @ X11)
% 0.41/0.61          | ~ (v2_pre_topc @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.41/0.61          | ~ (l1_pre_topc @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.41/0.61          | (v1_tsep_1 @ X9 @ X11)
% 0.41/0.61          | ~ (m1_pre_topc @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)) @ X11)
% 0.41/0.61          | ~ (v1_tsep_1 @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)) @ X11)
% 0.41/0.61          | ~ (l1_pre_topc @ X9)
% 0.41/0.61          | ~ (v2_pre_topc @ X9))),
% 0.41/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ sk_D)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_C)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_C)
% 0.41/0.61          | ~ (v1_tsep_1 @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.41/0.61          | (v1_tsep_1 @ sk_C @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ 
% 0.41/0.61               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['50', '52'])).
% 0.41/0.61  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.61          | (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v2_pre_topc @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.61  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('59', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.41/0.61  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.61          | (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v2_pre_topc @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.61  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('65', plain, ((v2_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.41/0.61  thf('66', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('70', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.61  thf('72', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.61  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_tsep_1 @ sk_D @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | (v1_tsep_1 @ sk_C @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['53', '59', '65', '66', '67', '68', '69', '74'])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_D)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_D)
% 0.41/0.61        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.41/0.61        | ~ (v1_tsep_1 @ sk_D @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['49', '75'])).
% 0.41/0.61  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('78', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.41/0.61  thf('79', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('80', plain, (((v1_tsep_1 @ sk_C @ sk_D) | ~ (v1_tsep_1 @ sk_D @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_D)
% 0.41/0.61        | ~ (l1_struct_0 @ sk_D)
% 0.41/0.61        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['48', '80'])).
% 0.41/0.61  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('83', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.41/0.61  thf('84', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('85', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('86', plain, ((l1_struct_0 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['84', '85'])).
% 0.41/0.61  thf('87', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['81', '82', '83', '86'])).
% 0.41/0.61  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('89', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_C)
% 0.41/0.61        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['13', '14', '15', '16', '19', '20', '32', '87', '88'])).
% 0.41/0.61  thf('90', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_C)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['89', '90'])).
% 0.41/0.61  thf('92', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.41/0.61  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('95', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.41/0.61      inference('clc', [status(thm)], ['93', '94'])).
% 0.41/0.61  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('97', plain, ((v2_struct_0 @ sk_C)),
% 0.41/0.61      inference('clc', [status(thm)], ['95', '96'])).
% 0.41/0.61  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
