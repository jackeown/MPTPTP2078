%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LT7Aw14WRA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  218 (1088 expanded)
%              Number of leaves         :   43 ( 329 expanded)
%              Depth                    :   26
%              Number of atoms          : 1952 (30143 expanded)
%              Number of equality atoms :   26 ( 774 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( v1_tsep_1 @ X33 @ X31 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X31 ) )
      | ( X34 != X35 )
      | ~ ( r1_tmap_1 @ X33 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36 ) @ X35 )
      | ( r1_tmap_1 @ X31 @ X30 @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ( r1_tmap_1 @ X31 @ X30 @ X36 @ X35 )
      | ~ ( r1_tmap_1 @ X33 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( v1_tsep_1 @ X33 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

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

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( ( k1_tsep_1 @ X25 @ X24 @ X24 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tsep_1 @ X0 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ X0 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','31','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('42',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

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

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_pre_topc @ X21 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('50',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('51',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['51','52'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','59'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['65','70','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['51','52'])).

thf('86',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('88',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['77','83','84','85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['51','52'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('95',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('97',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v3_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('101',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('102',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('104',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['102','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('109',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('111',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('112',plain,(
    ! [X9: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('115',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('124',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('125',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['51','52'])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['107','108'])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('134',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('137',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['132','138'])).

thf('140',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('143',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('145',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['132','138'])).

thf('147',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('148',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('149',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['131','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('152',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('153',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['86','87'])).

thf('154',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('158',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['132','138'])).

thf('159',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('160',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['99','100','101','109','160'])).

thf('162',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['89','161'])).

thf('163',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','53','162','163'])).

thf('165',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['0','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LT7Aw14WRA
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.60/1.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.78  % Solved by: fo/fo7.sh
% 1.60/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.78  % done 2072 iterations in 1.319s
% 1.60/1.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.78  % SZS output start Refutation
% 1.60/1.78  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.60/1.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.60/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.78  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.60/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.78  thf(sk_E_type, type, sk_E: $i).
% 1.60/1.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.60/1.78  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.60/1.78  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.60/1.78  thf(sk_G_type, type, sk_G: $i).
% 1.60/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.60/1.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.60/1.78  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.60/1.78  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.60/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.78  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.60/1.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.60/1.78  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.60/1.78  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.60/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.78  thf(sk_F_type, type, sk_F: $i).
% 1.60/1.78  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.60/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.78  thf(t88_tmap_1, conjecture,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.60/1.78             ( l1_pre_topc @ B ) ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.60/1.78               ( ![D:$i]:
% 1.60/1.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.60/1.78                   ( ![E:$i]:
% 1.60/1.78                     ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.78                         ( v1_funct_2 @
% 1.60/1.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.60/1.78                         ( m1_subset_1 @
% 1.60/1.78                           E @ 
% 1.60/1.78                           ( k1_zfmisc_1 @
% 1.60/1.78                             ( k2_zfmisc_1 @
% 1.60/1.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.60/1.78                       ( ( ( g1_pre_topc @
% 1.60/1.78                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.60/1.78                           ( D ) ) =>
% 1.60/1.78                         ( ![F:$i]:
% 1.60/1.78                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.60/1.78                             ( ![G:$i]:
% 1.60/1.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.60/1.78                                 ( ( ( ( F ) = ( G ) ) & 
% 1.60/1.78                                     ( r1_tmap_1 @
% 1.60/1.78                                       C @ B @ 
% 1.60/1.78                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.60/1.78                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.60/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.78    (~( ![A:$i]:
% 1.60/1.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.60/1.78            ( l1_pre_topc @ A ) ) =>
% 1.60/1.78          ( ![B:$i]:
% 1.60/1.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.60/1.78                ( l1_pre_topc @ B ) ) =>
% 1.60/1.78              ( ![C:$i]:
% 1.60/1.78                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.60/1.78                  ( ![D:$i]:
% 1.60/1.78                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.60/1.78                      ( ![E:$i]:
% 1.60/1.78                        ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.78                            ( v1_funct_2 @
% 1.60/1.78                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.60/1.78                            ( m1_subset_1 @
% 1.60/1.78                              E @ 
% 1.60/1.78                              ( k1_zfmisc_1 @
% 1.60/1.78                                ( k2_zfmisc_1 @
% 1.60/1.78                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.60/1.78                          ( ( ( g1_pre_topc @
% 1.60/1.78                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.60/1.78                              ( D ) ) =>
% 1.60/1.78                            ( ![F:$i]:
% 1.60/1.78                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.60/1.78                                ( ![G:$i]:
% 1.60/1.78                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.60/1.78                                    ( ( ( ( F ) = ( G ) ) & 
% 1.60/1.78                                        ( r1_tmap_1 @
% 1.60/1.78                                          C @ B @ 
% 1.60/1.78                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.60/1.78                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.60/1.78    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.60/1.78  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('1', plain,
% 1.60/1.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.60/1.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('2', plain, (((sk_F) = (sk_G))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('3', plain,
% 1.60/1.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.60/1.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.60/1.78      inference('demod', [status(thm)], ['1', '2'])).
% 1.60/1.78  thf('4', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_E @ 
% 1.60/1.78        (k1_zfmisc_1 @ 
% 1.60/1.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(t86_tmap_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.60/1.78             ( l1_pre_topc @ B ) ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.60/1.78               ( ![D:$i]:
% 1.60/1.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.60/1.78                   ( ![E:$i]:
% 1.60/1.78                     ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.78                         ( v1_funct_2 @
% 1.60/1.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.60/1.78                         ( m1_subset_1 @
% 1.60/1.78                           E @ 
% 1.60/1.78                           ( k1_zfmisc_1 @
% 1.60/1.78                             ( k2_zfmisc_1 @
% 1.60/1.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.60/1.78                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.60/1.78                         ( ![F:$i]:
% 1.60/1.78                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.60/1.78                             ( ![G:$i]:
% 1.60/1.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.60/1.78                                 ( ( ( F ) = ( G ) ) =>
% 1.60/1.78                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.60/1.78                                     ( r1_tmap_1 @
% 1.60/1.78                                       C @ B @ 
% 1.60/1.78                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.60/1.78  thf('5', plain,
% 1.60/1.78      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.60/1.78         ((v2_struct_0 @ X30)
% 1.60/1.78          | ~ (v2_pre_topc @ X30)
% 1.60/1.78          | ~ (l1_pre_topc @ X30)
% 1.60/1.78          | (v2_struct_0 @ X31)
% 1.60/1.78          | ~ (m1_pre_topc @ X31 @ X32)
% 1.60/1.78          | ~ (v1_tsep_1 @ X33 @ X31)
% 1.60/1.78          | ~ (m1_pre_topc @ X33 @ X31)
% 1.60/1.78          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X31))
% 1.60/1.78          | ((X34) != (X35))
% 1.60/1.78          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 1.60/1.78               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 1.60/1.78          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X34)
% 1.60/1.78          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 1.60/1.78          | ~ (m1_subset_1 @ X36 @ 
% 1.60/1.78               (k1_zfmisc_1 @ 
% 1.60/1.78                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 1.60/1.78          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 1.60/1.78          | ~ (v1_funct_1 @ X36)
% 1.60/1.78          | ~ (m1_pre_topc @ X33 @ X32)
% 1.60/1.78          | (v2_struct_0 @ X33)
% 1.60/1.78          | ~ (l1_pre_topc @ X32)
% 1.60/1.78          | ~ (v2_pre_topc @ X32)
% 1.60/1.78          | (v2_struct_0 @ X32))),
% 1.60/1.78      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.60/1.78  thf('6', plain,
% 1.60/1.78      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X35 : $i, X36 : $i]:
% 1.60/1.78         ((v2_struct_0 @ X32)
% 1.60/1.78          | ~ (v2_pre_topc @ X32)
% 1.60/1.78          | ~ (l1_pre_topc @ X32)
% 1.60/1.78          | (v2_struct_0 @ X33)
% 1.60/1.78          | ~ (m1_pre_topc @ X33 @ X32)
% 1.60/1.78          | ~ (v1_funct_1 @ X36)
% 1.60/1.78          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 1.60/1.78          | ~ (m1_subset_1 @ X36 @ 
% 1.60/1.78               (k1_zfmisc_1 @ 
% 1.60/1.78                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 1.60/1.78          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 1.60/1.78          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X35)
% 1.60/1.78          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 1.60/1.78               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 1.60/1.78          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X31))
% 1.60/1.78          | ~ (m1_pre_topc @ X33 @ X31)
% 1.60/1.78          | ~ (v1_tsep_1 @ X33 @ X31)
% 1.60/1.78          | ~ (m1_pre_topc @ X31 @ X32)
% 1.60/1.78          | (v2_struct_0 @ X31)
% 1.60/1.78          | ~ (l1_pre_topc @ X30)
% 1.60/1.78          | ~ (v2_pre_topc @ X30)
% 1.60/1.78          | (v2_struct_0 @ X30))),
% 1.60/1.78      inference('simplify', [status(thm)], ['5'])).
% 1.60/1.78  thf('7', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         ((v2_struct_0 @ sk_B)
% 1.60/1.78          | ~ (v2_pre_topc @ sk_B)
% 1.60/1.78          | ~ (l1_pre_topc @ sk_B)
% 1.60/1.78          | (v2_struct_0 @ sk_D)
% 1.60/1.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.60/1.78          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.60/1.78          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.60/1.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.60/1.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.60/1.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.60/1.78          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.60/1.78          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.60/1.78          | ~ (v1_funct_1 @ sk_E)
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ X0)
% 1.60/1.78          | (v2_struct_0 @ X1)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['4', '6'])).
% 1.60/1.78  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('10', plain,
% 1.60/1.78      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('12', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         ((v2_struct_0 @ sk_B)
% 1.60/1.78          | (v2_struct_0 @ sk_D)
% 1.60/1.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.60/1.78          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.60/1.78          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.60/1.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.60/1.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.60/1.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.60/1.78          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ X0)
% 1.60/1.78          | (v2_struct_0 @ X1)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0))),
% 1.60/1.78      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.60/1.78  thf('13', plain,
% 1.60/1.78      (((v2_struct_0 @ sk_A)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_A)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_A)
% 1.60/1.78        | (v2_struct_0 @ sk_C)
% 1.60/1.78        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.60/1.78        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.60/1.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.60/1.78        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.60/1.78        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.60/1.78        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.60/1.78        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.60/1.78        | (v2_struct_0 @ sk_D)
% 1.60/1.78        | (v2_struct_0 @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['3', '12'])).
% 1.60/1.78  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('18', plain, (((sk_F) = (sk_G))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['17', '18'])).
% 1.60/1.78  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('21', plain,
% 1.60/1.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(t2_tsep_1, axiom,
% 1.60/1.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.60/1.78  thf('22', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf(t25_tmap_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.60/1.78           ( ( k1_tsep_1 @ A @ B @ B ) =
% 1.60/1.78             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 1.60/1.78  thf('23', plain,
% 1.60/1.78      (![X24 : $i, X25 : $i]:
% 1.60/1.78         ((v2_struct_0 @ X24)
% 1.60/1.78          | ~ (m1_pre_topc @ X24 @ X25)
% 1.60/1.78          | ((k1_tsep_1 @ X25 @ X24 @ X24)
% 1.60/1.78              = (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 1.60/1.78          | ~ (l1_pre_topc @ X25)
% 1.60/1.78          | ~ (v2_pre_topc @ X25)
% 1.60/1.78          | (v2_struct_0 @ X25))),
% 1.60/1.78      inference('cnf', [status(esa)], [t25_tmap_1])).
% 1.60/1.78  thf('24', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ((k1_tsep_1 @ X0 @ X0 @ X0)
% 1.60/1.78              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.60/1.78          | (v2_struct_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.60/1.78  thf('25', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (((k1_tsep_1 @ X0 @ X0 @ X0)
% 1.60/1.78            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['24'])).
% 1.60/1.78  thf('26', plain,
% 1.60/1.78      ((((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D))
% 1.60/1.78        | ~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | (v2_struct_0 @ sk_C)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['21', '25'])).
% 1.60/1.78  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(dt_m1_pre_topc, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_pre_topc @ A ) =>
% 1.60/1.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.60/1.78  thf('28', plain,
% 1.60/1.78      (![X4 : $i, X5 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.60/1.78  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['27', '28'])).
% 1.60/1.78  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(cc1_pre_topc, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.60/1.78  thf('33', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X0 @ X1)
% 1.60/1.78          | (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X1)
% 1.60/1.78          | ~ (v2_pre_topc @ X1))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.60/1.78  thf('34', plain,
% 1.60/1.78      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.60/1.78  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('37', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('38', plain,
% 1.60/1.78      ((((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D)) | (v2_struct_0 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['26', '31', '37'])).
% 1.60/1.78  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('40', plain, (((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D))),
% 1.60/1.78      inference('clc', [status(thm)], ['38', '39'])).
% 1.60/1.78  thf('41', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf('42', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf(t22_tsep_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.60/1.78               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.60/1.78  thf('43', plain,
% 1.60/1.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.78         ((v2_struct_0 @ X21)
% 1.60/1.78          | ~ (m1_pre_topc @ X21 @ X22)
% 1.60/1.78          | (m1_pre_topc @ X21 @ (k1_tsep_1 @ X22 @ X21 @ X23))
% 1.60/1.78          | ~ (m1_pre_topc @ X23 @ X22)
% 1.60/1.78          | (v2_struct_0 @ X23)
% 1.60/1.78          | ~ (l1_pre_topc @ X22)
% 1.60/1.78          | ~ (v2_pre_topc @ X22)
% 1.60/1.78          | (v2_struct_0 @ X22))),
% 1.60/1.78      inference('cnf', [status(esa)], [t22_tsep_1])).
% 1.60/1.78  thf('44', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X1)
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ X0)
% 1.60/1.78          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 1.60/1.78          | (v2_struct_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['42', '43'])).
% 1.60/1.78  thf('45', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 1.60/1.78          | ~ (m1_pre_topc @ X1 @ X0)
% 1.60/1.78          | (v2_struct_0 @ X1)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['44'])).
% 1.60/1.78  thf('46', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['41', '45'])).
% 1.60/1.78  thf('47', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X0))
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v2_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['46'])).
% 1.60/1.78  thf('48', plain,
% 1.60/1.78      (((m1_pre_topc @ sk_C @ sk_D)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | (v2_struct_0 @ sk_C)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['40', '47'])).
% 1.60/1.78  thf('49', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('50', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('51', plain, (((m1_pre_topc @ sk_C @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.60/1.78  thf('52', plain, (~ (v2_struct_0 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.60/1.78      inference('clc', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.60/1.78      inference('clc', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf(d3_struct_0, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.60/1.78  thf('55', plain,
% 1.60/1.78      (![X2 : $i]:
% 1.60/1.78         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.60/1.78  thf('56', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf(t1_tsep_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_pre_topc @ A ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_pre_topc @ B @ A ) =>
% 1.60/1.78           ( m1_subset_1 @
% 1.60/1.78             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.60/1.78  thf('57', plain,
% 1.60/1.78      (![X19 : $i, X20 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X19 @ X20)
% 1.60/1.78          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.60/1.78          | ~ (l1_pre_topc @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.60/1.78  thf('58', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['56', '57'])).
% 1.60/1.78  thf('59', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['58'])).
% 1.60/1.78  thf('60', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('sup+', [status(thm)], ['55', '59'])).
% 1.60/1.78  thf(dt_l1_pre_topc, axiom,
% 1.60/1.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.60/1.78  thf('61', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.60/1.78  thf('62', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.60/1.78      inference('clc', [status(thm)], ['60', '61'])).
% 1.60/1.78  thf(t39_pre_topc, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_pre_topc @ A ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_pre_topc @ B @ A ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.60/1.78               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 1.60/1.78  thf('63', plain,
% 1.60/1.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X6 @ X7)
% 1.60/1.78          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 1.60/1.78          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.60/1.78          | ~ (l1_pre_topc @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t39_pre_topc])).
% 1.60/1.78  thf('64', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X1)
% 1.60/1.78          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.60/1.78      inference('sup-', [status(thm)], ['62', '63'])).
% 1.60/1.78  thf('65', plain,
% 1.60/1.78      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.60/1.78        | ~ (l1_pre_topc @ sk_D)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['54', '64'])).
% 1.60/1.78  thf('66', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('67', plain,
% 1.60/1.78      (![X4 : $i, X5 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.60/1.78  thf('68', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.60/1.78      inference('sup-', [status(thm)], ['66', '67'])).
% 1.60/1.78  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('70', plain, ((l1_pre_topc @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.60/1.78  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('72', plain,
% 1.60/1.78      ((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 1.60/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 1.60/1.78      inference('demod', [status(thm)], ['65', '70', '71'])).
% 1.60/1.78  thf('73', plain,
% 1.60/1.78      (![X2 : $i]:
% 1.60/1.78         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.60/1.78  thf(t16_tsep_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_pre_topc @ B @ A ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.60/1.78               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.60/1.78                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.60/1.78                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.60/1.78  thf('74', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X16 @ X17)
% 1.60/1.78          | ((X18) != (u1_struct_0 @ X16))
% 1.60/1.78          | ~ (v3_pre_topc @ X18 @ X17)
% 1.60/1.78          | (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (v2_pre_topc @ X17))),
% 1.60/1.78      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.60/1.78  thf('75', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X17)
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 1.60/1.78          | ~ (m1_pre_topc @ X16 @ X17))),
% 1.60/1.78      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.78  thf('76', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X1)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X1)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X1)
% 1.60/1.78          | ~ (l1_pre_topc @ X1)
% 1.60/1.78          | ~ (v2_pre_topc @ X1))),
% 1.60/1.78      inference('sup-', [status(thm)], ['73', '75'])).
% 1.60/1.78  thf('77', plain,
% 1.60/1.78      ((~ (v2_pre_topc @ sk_D)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_D)
% 1.60/1.78        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.60/1.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.60/1.78        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.60/1.78        | ~ (l1_struct_0 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['72', '76'])).
% 1.60/1.78  thf('78', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('79', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X0 @ X1)
% 1.60/1.78          | (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X1)
% 1.60/1.78          | ~ (v2_pre_topc @ X1))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.60/1.78  thf('80', plain,
% 1.60/1.78      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.60/1.78      inference('sup-', [status(thm)], ['78', '79'])).
% 1.60/1.78  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('83', plain, ((v2_pre_topc @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.60/1.78  thf('84', plain, ((l1_pre_topc @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.60/1.78  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.60/1.78      inference('clc', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf('86', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('87', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.60/1.78  thf('88', plain, ((l1_struct_0 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['86', '87'])).
% 1.60/1.78  thf('89', plain,
% 1.60/1.78      (((v1_tsep_1 @ sk_C @ sk_D)
% 1.60/1.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 1.60/1.78      inference('demod', [status(thm)], ['77', '83', '84', '85', '88'])).
% 1.60/1.78  thf('90', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['58'])).
% 1.60/1.78  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.60/1.78      inference('clc', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf('92', plain,
% 1.60/1.78      (![X19 : $i, X20 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X19 @ X20)
% 1.60/1.78          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.60/1.78          | ~ (l1_pre_topc @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.60/1.78  thf('93', plain,
% 1.60/1.78      ((~ (l1_pre_topc @ sk_D)
% 1.60/1.78        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['91', '92'])).
% 1.60/1.78  thf('94', plain, ((l1_pre_topc @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.60/1.78  thf('95', plain,
% 1.60/1.78      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.60/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 1.60/1.78      inference('demod', [status(thm)], ['93', '94'])).
% 1.60/1.78  thf(t33_tops_2, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_pre_topc @ A ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.60/1.78           ( ![C:$i]:
% 1.60/1.78             ( ( m1_pre_topc @ C @ A ) =>
% 1.60/1.78               ( ( v3_pre_topc @ B @ A ) =>
% 1.60/1.78                 ( ![D:$i]:
% 1.60/1.78                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 1.60/1.78                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 1.60/1.78  thf('96', plain,
% 1.60/1.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.60/1.78         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.60/1.78          | ~ (v3_pre_topc @ X10 @ X11)
% 1.60/1.78          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.60/1.78          | (v3_pre_topc @ X12 @ X13)
% 1.60/1.78          | ((X12) != (X10))
% 1.60/1.78          | ~ (m1_pre_topc @ X13 @ X11)
% 1.60/1.78          | ~ (l1_pre_topc @ X11))),
% 1.60/1.78      inference('cnf', [status(esa)], [t33_tops_2])).
% 1.60/1.78  thf('97', plain,
% 1.60/1.78      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X11)
% 1.60/1.78          | ~ (m1_pre_topc @ X13 @ X11)
% 1.60/1.78          | (v3_pre_topc @ X10 @ X13)
% 1.60/1.78          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.60/1.78          | ~ (v3_pre_topc @ X10 @ X11)
% 1.60/1.78          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.60/1.78      inference('simplify', [status(thm)], ['96'])).
% 1.60/1.78  thf('98', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.60/1.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['95', '97'])).
% 1.60/1.78  thf('99', plain,
% 1.60/1.78      ((~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 1.60/1.78        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.60/1.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['90', '98'])).
% 1.60/1.78  thf('100', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('101', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('102', plain,
% 1.60/1.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('103', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf(t11_tmap_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( l1_pre_topc @ A ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_pre_topc @ B @ A ) =>
% 1.60/1.78           ( ( v1_pre_topc @
% 1.60/1.78               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.60/1.78             ( m1_pre_topc @
% 1.60/1.78               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 1.60/1.78  thf('104', plain,
% 1.60/1.78      (![X14 : $i, X15 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X14 @ X15)
% 1.60/1.78          | (m1_pre_topc @ 
% 1.60/1.78             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)) @ X15)
% 1.60/1.78          | ~ (l1_pre_topc @ X15))),
% 1.60/1.78      inference('cnf', [status(esa)], [t11_tmap_1])).
% 1.60/1.78  thf('105', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | (m1_pre_topc @ 
% 1.60/1.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['103', '104'])).
% 1.60/1.78  thf('106', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_pre_topc @ 
% 1.60/1.78           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['105'])).
% 1.60/1.78  thf('107', plain, (((m1_pre_topc @ sk_D @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['102', '106'])).
% 1.60/1.78  thf('108', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('109', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['107', '108'])).
% 1.60/1.78  thf('110', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf('111', plain,
% 1.60/1.78      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.60/1.78  thf(fc10_tops_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.60/1.78  thf('112', plain,
% 1.60/1.78      (![X9 : $i]:
% 1.60/1.78         ((v3_pre_topc @ (k2_struct_0 @ X9) @ X9)
% 1.60/1.78          | ~ (l1_pre_topc @ X9)
% 1.60/1.78          | ~ (v2_pre_topc @ X9))),
% 1.60/1.78      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.60/1.78  thf('113', plain,
% 1.60/1.78      (![X2 : $i]:
% 1.60/1.78         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.60/1.78  thf('114', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['58'])).
% 1.60/1.78  thf('115', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X17)
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 1.60/1.78          | ~ (m1_pre_topc @ X16 @ X17))),
% 1.60/1.78      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.78  thf('116', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['114', '115'])).
% 1.60/1.78  thf('117', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['116'])).
% 1.60/1.78  thf('118', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['113', '117'])).
% 1.60/1.78  thf('119', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['112', '118'])).
% 1.60/1.78  thf('120', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['119'])).
% 1.60/1.78  thf('121', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['111', '120'])).
% 1.60/1.78  thf('122', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_struct_0 @ X0)
% 1.60/1.78          | (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['121'])).
% 1.60/1.78  thf('123', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['58'])).
% 1.60/1.78  thf('124', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X16 @ X17)
% 1.60/1.78          | ((X18) != (u1_struct_0 @ X16))
% 1.60/1.78          | ~ (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (m1_pre_topc @ X16 @ X17)
% 1.60/1.78          | (v3_pre_topc @ X18 @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (v2_pre_topc @ X17))),
% 1.60/1.78      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.60/1.78  thf('125', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X17)
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 1.60/1.78          | ~ (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (m1_pre_topc @ X16 @ X17))),
% 1.60/1.78      inference('simplify', [status(thm)], ['124'])).
% 1.60/1.78  thf('126', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['123', '125'])).
% 1.60/1.78  thf('127', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['126'])).
% 1.60/1.78  thf('128', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['122', '127'])).
% 1.60/1.78  thf('129', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['128'])).
% 1.60/1.78  thf('130', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['110', '129'])).
% 1.60/1.78  thf('131', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (l1_struct_0 @ X0)
% 1.60/1.78          | ~ (v2_pre_topc @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['130'])).
% 1.60/1.78  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.60/1.78      inference('clc', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['107', '108'])).
% 1.60/1.78  thf(t7_tsep_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_pre_topc @ B @ A ) =>
% 1.60/1.78           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 1.60/1.78  thf('134', plain,
% 1.60/1.78      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X27 @ X28)
% 1.60/1.78          | (m1_pre_topc @ X29 @ X28)
% 1.60/1.78          | ~ (m1_pre_topc @ X29 @ X27)
% 1.60/1.78          | ~ (l1_pre_topc @ X28)
% 1.60/1.78          | ~ (v2_pre_topc @ X28))),
% 1.60/1.78      inference('cnf', [status(esa)], [t7_tsep_1])).
% 1.60/1.78  thf('135', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ sk_C)
% 1.60/1.78          | ~ (l1_pre_topc @ sk_C)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.60/1.78          | (m1_pre_topc @ X0 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['133', '134'])).
% 1.60/1.78  thf('136', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('137', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('138', plain,
% 1.60/1.78      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.60/1.78  thf('139', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['132', '138'])).
% 1.60/1.78  thf('140', plain,
% 1.60/1.78      (![X19 : $i, X20 : $i]:
% 1.60/1.78         (~ (m1_pre_topc @ X19 @ X20)
% 1.60/1.78          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.60/1.78          | ~ (l1_pre_topc @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.60/1.78  thf('141', plain,
% 1.60/1.78      ((~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['139', '140'])).
% 1.60/1.78  thf('142', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('143', plain,
% 1.60/1.78      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.60/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['141', '142'])).
% 1.60/1.78  thf('144', plain,
% 1.60/1.78      (![X16 : $i, X17 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X17)
% 1.60/1.78          | ~ (l1_pre_topc @ X17)
% 1.60/1.78          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.60/1.78          | (v1_tsep_1 @ X16 @ X17)
% 1.60/1.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 1.60/1.78          | ~ (m1_pre_topc @ X16 @ X17))),
% 1.60/1.78      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.78  thf('145', plain,
% 1.60/1.78      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 1.60/1.78        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 1.60/1.78        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.60/1.78        | ~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['143', '144'])).
% 1.60/1.78  thf('146', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['132', '138'])).
% 1.60/1.78  thf('147', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('148', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('149', plain,
% 1.60/1.78      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 1.60/1.78        | (v1_tsep_1 @ sk_C @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 1.60/1.78  thf('150', plain,
% 1.60/1.78      ((~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_C)
% 1.60/1.78        | ~ (l1_struct_0 @ sk_C)
% 1.60/1.78        | (v1_tsep_1 @ sk_C @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['131', '149'])).
% 1.60/1.78  thf('151', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('152', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('153', plain, ((l1_struct_0 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['86', '87'])).
% 1.60/1.78  thf('154', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 1.60/1.78  thf('155', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v2_pre_topc @ X0)
% 1.60/1.78          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.60/1.78          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.60/1.78          | ~ (m1_pre_topc @ X0 @ X0)
% 1.60/1.78          | ~ (l1_pre_topc @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['126'])).
% 1.60/1.78  thf('156', plain,
% 1.60/1.78      ((~ (l1_pre_topc @ sk_C)
% 1.60/1.78        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.60/1.78        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 1.60/1.78        | ~ (v2_pre_topc @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['154', '155'])).
% 1.60/1.78  thf('157', plain, ((l1_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.60/1.78  thf('158', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['132', '138'])).
% 1.60/1.78  thf('159', plain, ((v2_pre_topc @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.60/1.78  thf('160', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)),
% 1.60/1.78      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 1.60/1.78  thf('161', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['99', '100', '101', '109', '160'])).
% 1.60/1.78  thf('162', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.60/1.78      inference('demod', [status(thm)], ['89', '161'])).
% 1.60/1.78  thf('163', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('164', plain,
% 1.60/1.78      (((v2_struct_0 @ sk_A)
% 1.60/1.78        | (v2_struct_0 @ sk_C)
% 1.60/1.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.60/1.78        | (v2_struct_0 @ sk_D)
% 1.60/1.78        | (v2_struct_0 @ sk_B))),
% 1.60/1.78      inference('demod', [status(thm)],
% 1.60/1.78                ['13', '14', '15', '16', '19', '20', '53', '162', '163'])).
% 1.60/1.78  thf('165', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('166', plain,
% 1.60/1.78      (((v2_struct_0 @ sk_B)
% 1.60/1.78        | (v2_struct_0 @ sk_D)
% 1.60/1.78        | (v2_struct_0 @ sk_C)
% 1.60/1.78        | (v2_struct_0 @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['164', '165'])).
% 1.60/1.78  thf('167', plain, (~ (v2_struct_0 @ sk_D)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('168', plain,
% 1.60/1.78      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['166', '167'])).
% 1.60/1.78  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('170', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.60/1.78      inference('clc', [status(thm)], ['168', '169'])).
% 1.60/1.78  thf('171', plain, (~ (v2_struct_0 @ sk_B)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('172', plain, ((v2_struct_0 @ sk_C)),
% 1.60/1.78      inference('clc', [status(thm)], ['170', '171'])).
% 1.60/1.78  thf('173', plain, ($false), inference('demod', [status(thm)], ['0', '172'])).
% 1.60/1.78  
% 1.60/1.78  % SZS output end Refutation
% 1.60/1.78  
% 1.60/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
