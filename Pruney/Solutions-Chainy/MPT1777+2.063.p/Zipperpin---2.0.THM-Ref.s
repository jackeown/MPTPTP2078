%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B3lXrPuXKF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:36 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 341 expanded)
%              Number of leaves         :   40 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          : 1373 (10733 expanded)
%              Number of equality atoms :   24 ( 286 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_pre_topc @ X17 @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k1_tsep_1 @ X21 @ X20 @ X20 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('47',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','63','68','71'])).

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

thf('73',plain,(
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

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['76','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('87',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('88',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('89',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('97',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['75','89','94','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['43','44'])).

thf('103',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','45','103','104'])).

thf('106',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B3lXrPuXKF
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 658 iterations in 0.306s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.54/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.77  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.54/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.77  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.54/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.77  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.54/0.77  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.77  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.54/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.77  thf(sk_F_type, type, sk_F: $i).
% 0.54/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.54/0.77  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.54/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.77  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.54/0.77  thf(sk_G_type, type, sk_G: $i).
% 0.54/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.77  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.54/0.77  thf(t88_tmap_1, conjecture,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.54/0.77             ( l1_pre_topc @ B ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.54/0.77               ( ![D:$i]:
% 0.54/0.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.54/0.77                   ( ![E:$i]:
% 0.54/0.77                     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.77                         ( v1_funct_2 @
% 0.54/0.77                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.77                         ( m1_subset_1 @
% 0.54/0.77                           E @ 
% 0.54/0.77                           ( k1_zfmisc_1 @
% 0.54/0.77                             ( k2_zfmisc_1 @
% 0.54/0.77                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.77                       ( ( ( g1_pre_topc @
% 0.54/0.77                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.54/0.77                           ( D ) ) =>
% 0.54/0.77                         ( ![F:$i]:
% 0.54/0.77                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.54/0.77                             ( ![G:$i]:
% 0.54/0.77                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.54/0.77                                 ( ( ( ( F ) = ( G ) ) & 
% 0.54/0.77                                     ( r1_tmap_1 @
% 0.54/0.77                                       C @ B @ 
% 0.54/0.77                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.54/0.77                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i]:
% 0.54/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.54/0.77            ( l1_pre_topc @ A ) ) =>
% 0.54/0.77          ( ![B:$i]:
% 0.54/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.54/0.77                ( l1_pre_topc @ B ) ) =>
% 0.54/0.77              ( ![C:$i]:
% 0.54/0.77                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.54/0.77                  ( ![D:$i]:
% 0.54/0.77                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.54/0.77                      ( ![E:$i]:
% 0.54/0.77                        ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.77                            ( v1_funct_2 @
% 0.54/0.77                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.77                            ( m1_subset_1 @
% 0.54/0.77                              E @ 
% 0.54/0.77                              ( k1_zfmisc_1 @
% 0.54/0.77                                ( k2_zfmisc_1 @
% 0.54/0.77                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.77                          ( ( ( g1_pre_topc @
% 0.54/0.77                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.54/0.77                              ( D ) ) =>
% 0.54/0.77                            ( ![F:$i]:
% 0.54/0.77                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.54/0.77                                ( ![G:$i]:
% 0.54/0.77                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.54/0.77                                    ( ( ( ( F ) = ( G ) ) & 
% 0.54/0.77                                        ( r1_tmap_1 @
% 0.54/0.77                                          C @ B @ 
% 0.54/0.77                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.54/0.77                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.54/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('1', plain,
% 0.54/0.77      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.54/0.77        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('2', plain, (((sk_F) = (sk_G))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.54/0.77        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.54/0.77      inference('demod', [status(thm)], ['1', '2'])).
% 0.54/0.77  thf('4', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_E @ 
% 0.54/0.77        (k1_zfmisc_1 @ 
% 0.54/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t86_tmap_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.54/0.77             ( l1_pre_topc @ B ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.54/0.77               ( ![D:$i]:
% 0.54/0.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.54/0.77                   ( ![E:$i]:
% 0.54/0.77                     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.77                         ( v1_funct_2 @
% 0.54/0.77                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.77                         ( m1_subset_1 @
% 0.54/0.77                           E @ 
% 0.54/0.77                           ( k1_zfmisc_1 @
% 0.54/0.77                             ( k2_zfmisc_1 @
% 0.54/0.77                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.77                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.54/0.77                         ( ![F:$i]:
% 0.54/0.77                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.54/0.77                             ( ![G:$i]:
% 0.54/0.77                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.54/0.77                                 ( ( ( F ) = ( G ) ) =>
% 0.54/0.77                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.54/0.77                                     ( r1_tmap_1 @
% 0.54/0.77                                       C @ B @ 
% 0.54/0.77                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.77         ((v2_struct_0 @ X25)
% 0.54/0.77          | ~ (v2_pre_topc @ X25)
% 0.54/0.77          | ~ (l1_pre_topc @ X25)
% 0.54/0.77          | (v2_struct_0 @ X26)
% 0.54/0.77          | ~ (m1_pre_topc @ X26 @ X27)
% 0.54/0.77          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.54/0.77          | ~ (m1_pre_topc @ X28 @ X26)
% 0.54/0.77          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 0.54/0.77          | ((X29) != (X30))
% 0.54/0.77          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.54/0.77               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.54/0.77          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 0.54/0.77          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.54/0.77          | ~ (m1_subset_1 @ X31 @ 
% 0.54/0.77               (k1_zfmisc_1 @ 
% 0.54/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.54/0.77          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.54/0.77          | ~ (v1_funct_1 @ X31)
% 0.54/0.77          | ~ (m1_pre_topc @ X28 @ X27)
% 0.54/0.77          | (v2_struct_0 @ X28)
% 0.54/0.77          | ~ (l1_pre_topc @ X27)
% 0.54/0.77          | ~ (v2_pre_topc @ X27)
% 0.54/0.77          | (v2_struct_0 @ X27))),
% 0.54/0.77      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.54/0.77  thf('6', plain,
% 0.54/0.77      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.54/0.77         ((v2_struct_0 @ X27)
% 0.54/0.77          | ~ (v2_pre_topc @ X27)
% 0.54/0.77          | ~ (l1_pre_topc @ X27)
% 0.54/0.77          | (v2_struct_0 @ X28)
% 0.54/0.77          | ~ (m1_pre_topc @ X28 @ X27)
% 0.54/0.77          | ~ (v1_funct_1 @ X31)
% 0.54/0.77          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.54/0.77          | ~ (m1_subset_1 @ X31 @ 
% 0.54/0.77               (k1_zfmisc_1 @ 
% 0.54/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.54/0.77          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.54/0.77          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.54/0.77          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.54/0.77               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.54/0.77          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.54/0.77          | ~ (m1_pre_topc @ X28 @ X26)
% 0.54/0.77          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.54/0.77          | ~ (m1_pre_topc @ X26 @ X27)
% 0.54/0.77          | (v2_struct_0 @ X26)
% 0.54/0.77          | ~ (l1_pre_topc @ X25)
% 0.54/0.77          | ~ (v2_pre_topc @ X25)
% 0.54/0.77          | (v2_struct_0 @ X25))),
% 0.54/0.77      inference('simplify', [status(thm)], ['5'])).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_B)
% 0.54/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.54/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.54/0.77          | (v2_struct_0 @ sk_D)
% 0.54/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.54/0.77          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.54/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.54/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.54/0.77          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.54/0.77               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.54/0.77          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.54/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.54/0.77          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.54/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.54/0.77          | (v2_struct_0 @ X1)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0)
% 0.54/0.77          | (v2_struct_0 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['4', '6'])).
% 0.54/0.77  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('10', plain,
% 0.54/0.77      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('12', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_B)
% 0.54/0.77          | (v2_struct_0 @ sk_D)
% 0.54/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.54/0.77          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.54/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.54/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.54/0.77          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.54/0.77               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.54/0.77          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.54/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.54/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.54/0.77          | (v2_struct_0 @ X1)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0)
% 0.54/0.77          | (v2_struct_0 @ X0))),
% 0.54/0.77      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.54/0.77  thf('13', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_C)
% 0.54/0.77        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.54/0.77        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.54/0.77        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.54/0.77        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.54/0.77        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.54/0.77        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.54/0.77        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_D)
% 0.54/0.77        | (v2_struct_0 @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['3', '12'])).
% 0.54/0.77  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('18', plain, (((sk_F) = (sk_G))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['17', '18'])).
% 0.54/0.77  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t22_tsep_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.54/0.77               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.54/0.77  thf('23', plain,
% 0.54/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.77         ((v2_struct_0 @ X17)
% 0.54/0.77          | ~ (m1_pre_topc @ X17 @ X18)
% 0.54/0.77          | (m1_pre_topc @ X17 @ (k1_tsep_1 @ X18 @ X17 @ X19))
% 0.54/0.77          | ~ (m1_pre_topc @ X19 @ X18)
% 0.54/0.77          | (v2_struct_0 @ X19)
% 0.54/0.77          | ~ (l1_pre_topc @ X18)
% 0.54/0.77          | ~ (v2_pre_topc @ X18)
% 0.54/0.77          | (v2_struct_0 @ X18))),
% 0.54/0.77      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.54/0.77  thf('24', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.54/0.77          | (v2_struct_0 @ X0)
% 0.54/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.54/0.77          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.54/0.77          | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.77  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('27', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | (v2_struct_0 @ X0)
% 0.54/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.54/0.77          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.54/0.77          | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.54/0.77  thf('28', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_C)
% 0.54/0.77        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.54/0.77        | (v2_struct_0 @ sk_C)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['21', '27'])).
% 0.54/0.77  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t25_tmap_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.54/0.77           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.54/0.77             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.54/0.77  thf('30', plain,
% 0.54/0.77      (![X20 : $i, X21 : $i]:
% 0.54/0.77         ((v2_struct_0 @ X20)
% 0.54/0.77          | ~ (m1_pre_topc @ X20 @ X21)
% 0.54/0.77          | ((k1_tsep_1 @ X21 @ X20 @ X20)
% 0.54/0.77              = (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.54/0.77          | ~ (l1_pre_topc @ X21)
% 0.54/0.77          | ~ (v2_pre_topc @ X21)
% 0.54/0.77          | (v2_struct_0 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.54/0.77        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.54/0.77            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.54/0.77        | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.77  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('34', plain,
% 0.54/0.77      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('35', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))
% 0.54/0.77        | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.54/0.77  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('37', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_C) | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D)))),
% 0.54/0.77      inference('clc', [status(thm)], ['35', '36'])).
% 0.54/0.77  thf('38', plain, (~ (v2_struct_0 @ sk_C)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('39', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.54/0.77      inference('clc', [status(thm)], ['37', '38'])).
% 0.54/0.77  thf('40', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_C)
% 0.54/0.77        | (m1_pre_topc @ sk_C @ sk_D)
% 0.54/0.77        | (v2_struct_0 @ sk_C)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['28', '39'])).
% 0.54/0.77  thf('41', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | (m1_pre_topc @ sk_C @ sk_D)
% 0.54/0.77        | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('simplify', [status(thm)], ['40'])).
% 0.54/0.77  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('43', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_D))),
% 0.54/0.77      inference('clc', [status(thm)], ['41', '42'])).
% 0.54/0.77  thf('44', plain, (~ (v2_struct_0 @ sk_C)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.54/0.77      inference('clc', [status(thm)], ['43', '44'])).
% 0.54/0.77  thf('46', plain,
% 0.54/0.77      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(fc10_tops_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.54/0.77  thf('47', plain,
% 0.54/0.77      (![X11 : $i]:
% 0.54/0.77         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.54/0.77          | ~ (l1_pre_topc @ X11)
% 0.54/0.77          | ~ (v2_pre_topc @ X11))),
% 0.54/0.77      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.54/0.77  thf(d3_struct_0, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.77  thf('48', plain,
% 0.54/0.77      (![X4 : $i]:
% 0.54/0.77         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.77  thf(dt_k2_subset_1, axiom,
% 0.54/0.77    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.77  thf('49', plain,
% 0.54/0.77      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.54/0.77  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.54/0.77  thf('50', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.54/0.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.54/0.77  thf('51', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.54/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.77  thf(t60_pre_topc, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.54/0.77             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.54/0.77           ( ( v3_pre_topc @
% 0.54/0.77               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.54/0.77             ( m1_subset_1 @
% 0.54/0.77               B @ 
% 0.54/0.77               ( k1_zfmisc_1 @
% 0.54/0.77                 ( u1_struct_0 @
% 0.54/0.77                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('52', plain,
% 0.54/0.77      (![X9 : $i, X10 : $i]:
% 0.54/0.77         (~ (v3_pre_topc @ X10 @ X9)
% 0.54/0.77          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.54/0.77          | (m1_subset_1 @ X10 @ 
% 0.54/0.77             (k1_zfmisc_1 @ 
% 0.54/0.77              (u1_struct_0 @ 
% 0.54/0.77               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))))
% 0.54/0.77          | ~ (l1_pre_topc @ X9)
% 0.54/0.77          | ~ (v2_pre_topc @ X9))),
% 0.54/0.77      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.54/0.77  thf('53', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (k1_zfmisc_1 @ 
% 0.54/0.77              (u1_struct_0 @ 
% 0.54/0.77               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.54/0.77          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['51', '52'])).
% 0.54/0.77  thf('54', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.54/0.77          | ~ (l1_struct_0 @ X0)
% 0.54/0.77          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (k1_zfmisc_1 @ 
% 0.54/0.77              (u1_struct_0 @ 
% 0.54/0.77               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['48', '53'])).
% 0.54/0.77  thf('55', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (k1_zfmisc_1 @ 
% 0.54/0.77              (u1_struct_0 @ 
% 0.54/0.77               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.54/0.77          | ~ (l1_struct_0 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['47', '54'])).
% 0.54/0.77  thf('56', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_struct_0 @ X0)
% 0.54/0.77          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (k1_zfmisc_1 @ 
% 0.54/0.77              (u1_struct_0 @ 
% 0.54/0.77               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0))),
% 0.54/0.77      inference('simplify', [status(thm)], ['55'])).
% 0.54/0.77  thf('57', plain,
% 0.54/0.77      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.54/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.54/0.77        | ~ (v2_pre_topc @ sk_C)
% 0.54/0.77        | ~ (l1_pre_topc @ sk_C)
% 0.54/0.77        | ~ (l1_struct_0 @ sk_C))),
% 0.54/0.77      inference('sup+', [status(thm)], ['46', '56'])).
% 0.54/0.77  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(cc1_pre_topc, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.54/0.77  thf('59', plain,
% 0.54/0.77      (![X2 : $i, X3 : $i]:
% 0.54/0.77         (~ (m1_pre_topc @ X2 @ X3)
% 0.54/0.77          | (v2_pre_topc @ X2)
% 0.54/0.77          | ~ (l1_pre_topc @ X3)
% 0.54/0.77          | ~ (v2_pre_topc @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.54/0.77  thf('60', plain,
% 0.54/0.77      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['58', '59'])).
% 0.54/0.77  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('63', plain, ((v2_pre_topc @ sk_C)),
% 0.54/0.77      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.54/0.77  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(dt_m1_pre_topc, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( l1_pre_topc @ A ) =>
% 0.54/0.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.54/0.77  thf('65', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.54/0.77  thf('66', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.54/0.77      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.77  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 0.54/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.54/0.77  thf('69', plain, ((l1_pre_topc @ sk_C)),
% 0.54/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.54/0.77  thf(dt_l1_pre_topc, axiom,
% 0.54/0.77    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.54/0.77  thf('70', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.77  thf('71', plain, ((l1_struct_0 @ sk_C)),
% 0.54/0.77      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.77  thf('72', plain,
% 0.54/0.77      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.54/0.77      inference('demod', [status(thm)], ['57', '63', '68', '71'])).
% 0.54/0.77  thf(t16_tsep_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_pre_topc @ B @ A ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.54/0.77                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.54/0.77                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('73', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.77         (~ (m1_pre_topc @ X12 @ X13)
% 0.54/0.77          | ((X14) != (u1_struct_0 @ X12))
% 0.54/0.77          | ~ (v3_pre_topc @ X14 @ X13)
% 0.54/0.77          | (v1_tsep_1 @ X12 @ X13)
% 0.54/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.54/0.77          | ~ (l1_pre_topc @ X13)
% 0.54/0.77          | ~ (v2_pre_topc @ X13))),
% 0.54/0.77      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.54/0.77  thf('74', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i]:
% 0.54/0.77         (~ (v2_pre_topc @ X13)
% 0.54/0.77          | ~ (l1_pre_topc @ X13)
% 0.54/0.77          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.54/0.77               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.54/0.77          | (v1_tsep_1 @ X12 @ X13)
% 0.54/0.77          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.54/0.77          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.54/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.54/0.77  thf('75', plain,
% 0.54/0.77      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.54/0.77        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.54/0.77        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.54/0.77        | ~ (l1_pre_topc @ sk_D)
% 0.54/0.77        | ~ (v2_pre_topc @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['72', '74'])).
% 0.54/0.77  thf('76', plain,
% 0.54/0.77      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('77', plain,
% 0.54/0.77      (![X11 : $i]:
% 0.54/0.77         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.54/0.77          | ~ (l1_pre_topc @ X11)
% 0.54/0.77          | ~ (v2_pre_topc @ X11))),
% 0.54/0.77      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.54/0.77  thf('78', plain,
% 0.54/0.77      (![X4 : $i]:
% 0.54/0.77         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.77  thf('79', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.54/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.77  thf('80', plain,
% 0.54/0.77      (![X9 : $i, X10 : $i]:
% 0.54/0.77         (~ (v3_pre_topc @ X10 @ X9)
% 0.54/0.77          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.54/0.77          | (v3_pre_topc @ X10 @ 
% 0.54/0.77             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.54/0.77          | ~ (l1_pre_topc @ X9)
% 0.54/0.77          | ~ (v2_pre_topc @ X9))),
% 0.54/0.77      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.54/0.77  thf('81', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.54/0.77          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.77  thf('82', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.54/0.77          | ~ (l1_struct_0 @ X0)
% 0.54/0.77          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['78', '81'])).
% 0.54/0.77  thf('83', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0)
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.54/0.77          | ~ (l1_struct_0 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['77', '82'])).
% 0.54/0.77  thf('84', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_struct_0 @ X0)
% 0.54/0.77          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.54/0.77             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.54/0.77          | ~ (l1_pre_topc @ X0)
% 0.54/0.77          | ~ (v2_pre_topc @ X0))),
% 0.54/0.77      inference('simplify', [status(thm)], ['83'])).
% 0.54/0.77  thf('85', plain,
% 0.54/0.77      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.54/0.77        | ~ (v2_pre_topc @ sk_C)
% 0.54/0.77        | ~ (l1_pre_topc @ sk_C)
% 0.54/0.77        | ~ (l1_struct_0 @ sk_C))),
% 0.54/0.77      inference('sup+', [status(thm)], ['76', '84'])).
% 0.54/0.77  thf('86', plain, ((v2_pre_topc @ sk_C)),
% 0.54/0.77      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.54/0.77  thf('87', plain, ((l1_pre_topc @ sk_C)),
% 0.54/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.54/0.77  thf('88', plain, ((l1_struct_0 @ sk_C)),
% 0.54/0.77      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.77  thf('89', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.54/0.77      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.54/0.77  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('91', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.54/0.77  thf('92', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['90', '91'])).
% 0.54/0.77  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('94', plain, ((l1_pre_topc @ sk_D)),
% 0.54/0.77      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.77  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('96', plain,
% 0.54/0.77      (![X2 : $i, X3 : $i]:
% 0.54/0.77         (~ (m1_pre_topc @ X2 @ X3)
% 0.54/0.77          | (v2_pre_topc @ X2)
% 0.54/0.77          | ~ (l1_pre_topc @ X3)
% 0.54/0.77          | ~ (v2_pre_topc @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.54/0.77  thf('97', plain,
% 0.54/0.77      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.54/0.77      inference('sup-', [status(thm)], ['95', '96'])).
% 0.54/0.77  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('100', plain, ((v2_pre_topc @ sk_D)),
% 0.54/0.77      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.54/0.77  thf('101', plain,
% 0.54/0.77      ((~ (m1_pre_topc @ sk_C @ sk_D) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.54/0.77      inference('demod', [status(thm)], ['75', '89', '94', '100'])).
% 0.54/0.77  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.54/0.77      inference('clc', [status(thm)], ['43', '44'])).
% 0.54/0.77  thf('103', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.54/0.77      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.77  thf('104', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('105', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_C)
% 0.54/0.77        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.54/0.77        | (v2_struct_0 @ sk_D)
% 0.54/0.77        | (v2_struct_0 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)],
% 0.54/0.77                ['13', '14', '15', '16', '19', '20', '45', '103', '104'])).
% 0.54/0.77  thf('106', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('107', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_D)
% 0.54/0.77        | (v2_struct_0 @ sk_C)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['105', '106'])).
% 0.54/0.77  thf('108', plain, (~ (v2_struct_0 @ sk_D)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('109', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['107', '108'])).
% 0.54/0.77  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('111', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.54/0.77      inference('clc', [status(thm)], ['109', '110'])).
% 0.54/0.77  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('113', plain, ((v2_struct_0 @ sk_C)),
% 0.54/0.77      inference('clc', [status(thm)], ['111', '112'])).
% 0.54/0.77  thf('114', plain, ($false), inference('demod', [status(thm)], ['0', '113'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.54/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
