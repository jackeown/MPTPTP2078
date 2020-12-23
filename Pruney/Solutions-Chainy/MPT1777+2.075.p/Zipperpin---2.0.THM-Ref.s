%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aNU7rToxcM

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 356 expanded)
%              Number of leaves         :   40 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          : 1268 (10066 expanded)
%              Number of equality atoms :   16 ( 252 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

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

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49'])).

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

thf('51',plain,(
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

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['54','59'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('61',plain,(
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

thf('62',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

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

thf('67',plain,(
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

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('77',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('82',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('83',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('84',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['74','80','81','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['54','59'])).

thf('87',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('88',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('89',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','85','86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','93','94'])).

thf('96',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aNU7rToxcM
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 369 iterations in 0.153s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.60  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
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
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.60        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('2', plain, (((sk_F) = (sk_G))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.41/0.60        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t86_tmap_1, axiom,
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
% 0.41/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X25)
% 0.41/0.61          | ~ (v2_pre_topc @ X25)
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | (v2_struct_0 @ X26)
% 0.41/0.61          | ~ (m1_pre_topc @ X26 @ X27)
% 0.41/0.61          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.41/0.61          | ~ (m1_pre_topc @ X28 @ X26)
% 0.41/0.61          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 0.41/0.61          | ((X29) != (X30))
% 0.41/0.61          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.41/0.61               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.41/0.61          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.41/0.61          | ~ (m1_subset_1 @ X31 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.41/0.61          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.41/0.61          | ~ (v1_funct_1 @ X31)
% 0.41/0.61          | ~ (m1_pre_topc @ X28 @ X27)
% 0.41/0.61          | (v2_struct_0 @ X28)
% 0.41/0.61          | ~ (l1_pre_topc @ X27)
% 0.41/0.61          | ~ (v2_pre_topc @ X27)
% 0.41/0.61          | (v2_struct_0 @ X27))),
% 0.41/0.61      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X27)
% 0.41/0.61          | ~ (v2_pre_topc @ X27)
% 0.41/0.61          | ~ (l1_pre_topc @ X27)
% 0.41/0.61          | (v2_struct_0 @ X28)
% 0.41/0.61          | ~ (m1_pre_topc @ X28 @ X27)
% 0.41/0.61          | ~ (v1_funct_1 @ X31)
% 0.41/0.61          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.41/0.61          | ~ (m1_subset_1 @ X31 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.41/0.61          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.41/0.61          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.41/0.61               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.41/0.61          | ~ (m1_pre_topc @ X28 @ X26)
% 0.41/0.61          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.41/0.61          | ~ (m1_pre_topc @ X26 @ X27)
% 0.41/0.61          | (v2_struct_0 @ X26)
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | ~ (v2_pre_topc @ X25)
% 0.41/0.61          | (v2_struct_0 @ X25))),
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
% 0.41/0.61      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
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
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X8)
% 0.41/0.61          | ~ (m1_pre_topc @ X9 @ X8)
% 0.41/0.61          | (m1_pre_topc @ X9 @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.41/0.61          | ~ (l1_pre_topc @ X9))),
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
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf(t59_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @
% 0.41/0.61             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.41/0.61           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X6 @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.41/0.61          | (m1_pre_topc @ X6 @ X7)
% 0.41/0.61          | ~ (l1_pre_topc @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (m1_pre_topc @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.61        | (m1_pre_topc @ 
% 0.41/0.61           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '36'])).
% 0.41/0.61  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.61  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('42', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 0.41/0.61  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '31'])).
% 0.41/0.61  thf(t35_borsuk_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      (![X20 : $i, X21 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X20 @ X21)
% 0.41/0.61          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.41/0.61          | ~ (l1_pre_topc @ X21))),
% 0.41/0.61      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_D)
% 0.41/0.61        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('50', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.61  thf(t19_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.61               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.41/0.61                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.61         (~ (v1_tsep_1 @ X14 @ X15)
% 0.41/0.61          | ~ (m1_pre_topc @ X14 @ X15)
% 0.41/0.61          | ~ (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 0.41/0.61          | (v1_tsep_1 @ X14 @ X16)
% 0.41/0.61          | ~ (m1_pre_topc @ X16 @ X15)
% 0.41/0.61          | (v2_struct_0 @ X16)
% 0.41/0.61          | ~ (l1_pre_topc @ X15)
% 0.41/0.61          | ~ (v2_pre_topc @ X15)
% 0.41/0.61          | (v2_struct_0 @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (v2_struct_0 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.41/0.61          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.41/0.61        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.41/0.61        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_C)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_C)
% 0.41/0.61        | (v2_struct_0 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '52'])).
% 0.41/0.61  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '31'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X6 @ 
% 0.41/0.61             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.41/0.61          | (m1_pre_topc @ X6 @ X7)
% 0.41/0.61          | ~ (l1_pre_topc @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_C)
% 0.41/0.61          | (m1_pre_topc @ X0 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.61  thf('58', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.41/0.61  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '59'])).
% 0.41/0.61  thf(fc10_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X10 : $i]:
% 0.41/0.61         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.41/0.61          | ~ (l1_pre_topc @ X10)
% 0.41/0.61          | ~ (v2_pre_topc @ X10))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.41/0.61  thf(d3_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X2 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.61  thf(t1_tsep_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.61           ( m1_subset_1 @
% 0.41/0.61             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X17 @ X18)
% 0.41/0.61          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | ~ (l1_pre_topc @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['65'])).
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
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X11 @ X12)
% 0.41/0.61          | ((X13) != (u1_struct_0 @ X11))
% 0.41/0.61          | ~ (v3_pre_topc @ X13 @ X12)
% 0.41/0.61          | (v1_tsep_1 @ X11 @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.61          | ~ (l1_pre_topc @ X12)
% 0.41/0.61          | ~ (v2_pre_topc @ X12))),
% 0.41/0.61      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X12)
% 0.41/0.61          | ~ (l1_pre_topc @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.41/0.61          | (v1_tsep_1 @ X11 @ X12)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.41/0.61          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.41/0.61      inference('simplify', [status(thm)], ['67'])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['66', '68'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['62', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['61', '71'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_struct_0 @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ X0)
% 0.41/0.61          | (v1_tsep_1 @ X0 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['72'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      ((~ (v2_pre_topc @ sk_C)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_C)
% 0.41/0.61        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.41/0.61        | ~ (l1_struct_0 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '73'])).
% 0.41/0.61  thf('75', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (m1_pre_topc @ X0 @ X1)
% 0.41/0.61          | (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v2_pre_topc @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.61  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('80', plain, ((v2_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.41/0.61  thf('81', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('82', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('83', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('84', plain, ((l1_struct_0 @ sk_C)),
% 0.41/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['74', '80', '81', '84'])).
% 0.41/0.61  thf('86', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '59'])).
% 0.41/0.61  thf('87', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('88', plain, ((v2_pre_topc @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.41/0.61  thf('89', plain,
% 0.41/0.61      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['53', '85', '86', '87', '88'])).
% 0.41/0.61  thf('90', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('91', plain, (((v2_struct_0 @ sk_C) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.41/0.61      inference('clc', [status(thm)], ['89', '90'])).
% 0.41/0.61  thf('92', plain, (~ (v2_struct_0 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('93', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.41/0.61      inference('clc', [status(thm)], ['91', '92'])).
% 0.41/0.61  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('95', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_C)
% 0.41/0.61        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['13', '14', '15', '16', '19', '20', '32', '93', '94'])).
% 0.41/0.61  thf('96', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('97', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_D)
% 0.41/0.61        | (v2_struct_0 @ sk_C)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['95', '96'])).
% 0.41/0.61  thf('98', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('99', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.41/0.61  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('101', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.41/0.61      inference('clc', [status(thm)], ['99', '100'])).
% 0.41/0.61  thf('102', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('103', plain, ((v2_struct_0 @ sk_C)),
% 0.41/0.61      inference('clc', [status(thm)], ['101', '102'])).
% 0.41/0.61  thf('104', plain, ($false), inference('demod', [status(thm)], ['0', '103'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
