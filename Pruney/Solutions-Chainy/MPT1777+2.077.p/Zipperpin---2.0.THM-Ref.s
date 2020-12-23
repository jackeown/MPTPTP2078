%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bb9viA7b4z

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 551 expanded)
%              Number of leaves         :   37 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          : 1467 (15157 expanded)
%              Number of equality atoms :   19 ( 378 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','40'])).

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

thf('42',plain,(
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

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['44','45','46','52'])).

thf('54',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','40'])).

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

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ X14 @ X15 )
      | ( X14 != X12 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v3_pre_topc @ X12 @ X15 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('64',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('65',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('72',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('76',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('92',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('93',plain,(
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

thf('94',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('105',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('110',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('111',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('112',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['102','108','109','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('115',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('116',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['90','91','113','114','115'])).

thf('117',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['62','63','64','74','116'])).

thf('118',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['53','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','118','119'])).

thf('121',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bb9viA7b4z
% 0.15/0.38  % Computer   : n002.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 19:09:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 445 iterations in 0.196s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.51/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.69  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.51/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.51/0.69  thf(sk_G_type, type, sk_G: $i).
% 0.51/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.69  thf(sk_F_type, type, sk_F: $i).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.69  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.51/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.69  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.69  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.51/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.69  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.51/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.69  thf(t88_tmap_1, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.69             ( l1_pre_topc @ B ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.69               ( ![D:$i]:
% 0.51/0.69                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.69                   ( ![E:$i]:
% 0.51/0.69                     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.69                         ( v1_funct_2 @
% 0.51/0.69                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                         ( m1_subset_1 @
% 0.51/0.69                           E @ 
% 0.51/0.69                           ( k1_zfmisc_1 @
% 0.51/0.69                             ( k2_zfmisc_1 @
% 0.51/0.69                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69                       ( ( ( g1_pre_topc @
% 0.51/0.69                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.51/0.69                           ( D ) ) =>
% 0.51/0.69                         ( ![F:$i]:
% 0.51/0.69                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.69                             ( ![G:$i]:
% 0.51/0.69                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.69                                 ( ( ( ( F ) = ( G ) ) & 
% 0.51/0.69                                     ( r1_tmap_1 @
% 0.51/0.69                                       C @ B @ 
% 0.51/0.69                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.51/0.69                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.69            ( l1_pre_topc @ A ) ) =>
% 0.51/0.69          ( ![B:$i]:
% 0.51/0.69            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.69                ( l1_pre_topc @ B ) ) =>
% 0.51/0.69              ( ![C:$i]:
% 0.51/0.69                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.69                  ( ![D:$i]:
% 0.51/0.69                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.69                      ( ![E:$i]:
% 0.51/0.69                        ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.69                            ( v1_funct_2 @
% 0.51/0.69                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                            ( m1_subset_1 @
% 0.51/0.69                              E @ 
% 0.51/0.69                              ( k1_zfmisc_1 @
% 0.51/0.69                                ( k2_zfmisc_1 @
% 0.51/0.69                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69                          ( ( ( g1_pre_topc @
% 0.51/0.69                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.51/0.69                              ( D ) ) =>
% 0.51/0.69                            ( ![F:$i]:
% 0.51/0.69                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.69                                ( ![G:$i]:
% 0.51/0.69                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.69                                    ( ( ( ( F ) = ( G ) ) & 
% 0.51/0.69                                        ( r1_tmap_1 @
% 0.51/0.69                                          C @ B @ 
% 0.51/0.69                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.51/0.69                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.51/0.69  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.51/0.69        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('2', plain, (((sk_F) = (sk_G))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.51/0.69        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.51/0.69      inference('demod', [status(thm)], ['1', '2'])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_E @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t86_tmap_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.69             ( l1_pre_topc @ B ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.69               ( ![D:$i]:
% 0.51/0.69                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.69                   ( ![E:$i]:
% 0.51/0.69                     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.69                         ( v1_funct_2 @
% 0.51/0.69                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                         ( m1_subset_1 @
% 0.51/0.69                           E @ 
% 0.51/0.69                           ( k1_zfmisc_1 @
% 0.51/0.69                             ( k2_zfmisc_1 @
% 0.51/0.69                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.51/0.69                         ( ![F:$i]:
% 0.51/0.69                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.51/0.69                             ( ![G:$i]:
% 0.51/0.69                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.51/0.69                                 ( ( ( F ) = ( G ) ) =>
% 0.51/0.69                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.51/0.69                                     ( r1_tmap_1 @
% 0.51/0.69                                       C @ B @ 
% 0.51/0.69                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf('5', plain,
% 0.51/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X25)
% 0.51/0.69          | ~ (v2_pre_topc @ X25)
% 0.51/0.69          | ~ (l1_pre_topc @ X25)
% 0.51/0.69          | (v2_struct_0 @ X26)
% 0.51/0.69          | ~ (m1_pre_topc @ X26 @ X27)
% 0.51/0.69          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.51/0.69          | ~ (m1_pre_topc @ X28 @ X26)
% 0.51/0.69          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 0.51/0.69          | ((X29) != (X30))
% 0.51/0.69          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.51/0.69               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.51/0.69          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 0.51/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ 
% 0.51/0.69               (k1_zfmisc_1 @ 
% 0.51/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.51/0.69          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.51/0.69          | ~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (m1_pre_topc @ X28 @ X27)
% 0.51/0.69          | (v2_struct_0 @ X28)
% 0.51/0.69          | ~ (l1_pre_topc @ X27)
% 0.51/0.69          | ~ (v2_pre_topc @ X27)
% 0.51/0.69          | (v2_struct_0 @ X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X27)
% 0.51/0.69          | ~ (v2_pre_topc @ X27)
% 0.51/0.69          | ~ (l1_pre_topc @ X27)
% 0.51/0.69          | (v2_struct_0 @ X28)
% 0.51/0.69          | ~ (m1_pre_topc @ X28 @ X27)
% 0.51/0.69          | ~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ 
% 0.51/0.69               (k1_zfmisc_1 @ 
% 0.51/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.51/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.51/0.69          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.51/0.69          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.51/0.69               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.51/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.51/0.69          | ~ (m1_pre_topc @ X28 @ X26)
% 0.51/0.69          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.51/0.69          | ~ (m1_pre_topc @ X26 @ X27)
% 0.51/0.69          | (v2_struct_0 @ X26)
% 0.51/0.69          | ~ (l1_pre_topc @ X25)
% 0.51/0.69          | ~ (v2_pre_topc @ X25)
% 0.51/0.69          | (v2_struct_0 @ X25))),
% 0.51/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B)
% 0.51/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.51/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.51/0.69          | (v2_struct_0 @ sk_D)
% 0.51/0.69          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.69          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.51/0.69          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.51/0.69          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.51/0.69               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.51/0.69          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.69          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.69          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_pre_topc @ X0)
% 0.51/0.69          | ~ (v2_pre_topc @ X0)
% 0.51/0.69          | (v2_struct_0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['4', '6'])).
% 0.51/0.69  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B)
% 0.51/0.69          | (v2_struct_0 @ sk_D)
% 0.51/0.69          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.69          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.51/0.69          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.51/0.69          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.51/0.69               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.51/0.69          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.69          | ~ (m1_pre_topc @ X1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_pre_topc @ X0)
% 0.51/0.69          | ~ (v2_pre_topc @ X0)
% 0.51/0.69          | (v2_struct_0 @ X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (((v2_struct_0 @ sk_A)
% 0.51/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.69        | (v2_struct_0 @ sk_C)
% 0.51/0.69        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.69        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.51/0.69        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.69        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.51/0.69        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.51/0.69        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.51/0.69        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.51/0.69        | (v2_struct_0 @ sk_D)
% 0.51/0.69        | (v2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['3', '12'])).
% 0.51/0.69  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('18', plain, (((sk_F) = (sk_G))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.69  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('21', plain,
% 0.51/0.69      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t2_tsep_1, axiom,
% 0.51/0.69    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.69  thf(t65_pre_topc, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_pre_topc @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( l1_pre_topc @ B ) =>
% 0.51/0.69           ( ( m1_pre_topc @ A @ B ) <=>
% 0.51/0.69             ( m1_pre_topc @
% 0.51/0.69               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (~ (l1_pre_topc @ X9)
% 0.51/0.69          | ~ (m1_pre_topc @ X10 @ X9)
% 0.51/0.69          | (m1_pre_topc @ X10 @ 
% 0.51/0.69             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.51/0.69          | ~ (l1_pre_topc @ X10))),
% 0.51/0.69      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (l1_pre_topc @ X0)
% 0.51/0.69          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_pre_topc @ X0 @ 
% 0.51/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_pre_topc @ X0 @ 
% 0.51/0.70           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['24'])).
% 0.51/0.70  thf('26', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup+', [status(thm)], ['21', '25'])).
% 0.51/0.70  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_m1_pre_topc, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_pre_topc @ A ) =>
% 0.51/0.70       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.51/0.70  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.70  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['26', '31'])).
% 0.51/0.70  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['26', '31'])).
% 0.51/0.70  thf(t1_tsep_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_pre_topc @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.51/0.70           ( m1_subset_1 @
% 0.51/0.70             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (![X19 : $i, X20 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X19 @ X20)
% 0.51/0.70          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.51/0.70          | ~ (l1_pre_topc @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      ((~ (l1_pre_topc @ sk_D)
% 0.51/0.70        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.70  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.51/0.70  thf('38', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.70  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.51/0.70      inference('demod', [status(thm)], ['35', '40'])).
% 0.51/0.70  thf(t16_tsep_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.51/0.70                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.51/0.70                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | ((X18) != (u1_struct_0 @ X16))
% 0.51/0.70          | ~ (v3_pre_topc @ X18 @ X17)
% 0.51/0.70          | (v1_tsep_1 @ X16 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (v2_pre_topc @ X17))),
% 0.51/0.70      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i]:
% 0.51/0.70         (~ (v2_pre_topc @ X17)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.51/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | (v1_tsep_1 @ X16 @ X17)
% 0.51/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.51/0.70          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.51/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.51/0.70        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.51/0.70        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_D)
% 0.51/0.70        | ~ (v2_pre_topc @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['41', '43'])).
% 0.51/0.70  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['26', '31'])).
% 0.51/0.70  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.51/0.70  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc1_pre_topc, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.51/0.70  thf('48', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.70          | (v2_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X1)
% 0.51/0.70          | ~ (v2_pre_topc @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.70  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('52', plain, ((v2_pre_topc @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.51/0.70  thf('53', plain,
% 0.51/0.70      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.51/0.70        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.51/0.70      inference('demod', [status(thm)], ['44', '45', '46', '52'])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.70  thf('55', plain,
% 0.51/0.70      (![X19 : $i, X20 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X19 @ X20)
% 0.51/0.70          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.51/0.70          | ~ (l1_pre_topc @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.51/0.70  thf('56', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.51/0.70  thf('57', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.51/0.70      inference('demod', [status(thm)], ['35', '40'])).
% 0.51/0.70  thf(t33_tops_2, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_pre_topc @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_pre_topc @ C @ A ) =>
% 0.51/0.70               ( ( v3_pre_topc @ B @ A ) =>
% 0.51/0.70                 ( ![D:$i]:
% 0.51/0.70                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.51/0.70                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.51/0.70          | ~ (v3_pre_topc @ X12 @ X13)
% 0.51/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.51/0.70          | (v3_pre_topc @ X14 @ X15)
% 0.51/0.70          | ((X14) != (X12))
% 0.51/0.70          | ~ (m1_pre_topc @ X15 @ X13)
% 0.51/0.70          | ~ (l1_pre_topc @ X13))),
% 0.51/0.70      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.51/0.70  thf('60', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X13)
% 0.51/0.70          | ~ (m1_pre_topc @ X15 @ X13)
% 0.51/0.70          | (v3_pre_topc @ X12 @ X15)
% 0.51/0.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.51/0.70          | ~ (v3_pre_topc @ X12 @ X13)
% 0.51/0.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.51/0.70      inference('simplify', [status(thm)], ['59'])).
% 0.51/0.70  thf('61', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.51/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.51/0.70          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.51/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['58', '60'])).
% 0.51/0.70  thf('62', plain,
% 0.51/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.51/0.70        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.51/0.70        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.51/0.70        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['57', '61'])).
% 0.51/0.70  thf('63', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('64', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('65', plain,
% 0.51/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('66', plain,
% 0.51/0.70      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.51/0.70  thf('67', plain,
% 0.51/0.70      (![X9 : $i, X10 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X9)
% 0.51/0.70          | ~ (m1_pre_topc @ X10 @ 
% 0.51/0.70               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.51/0.70          | (m1_pre_topc @ X10 @ X9)
% 0.51/0.70          | ~ (l1_pre_topc @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.51/0.70  thf('68', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ 
% 0.51/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ 
% 0.51/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.51/0.70          | (m1_pre_topc @ 
% 0.51/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.70  thf('69', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_pre_topc @ 
% 0.51/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ 
% 0.51/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.51/0.70      inference('simplify', [status(thm)], ['68'])).
% 0.51/0.70  thf('70', plain,
% 0.51/0.70      ((~ (l1_pre_topc @ sk_D)
% 0.51/0.70        | (m1_pre_topc @ 
% 0.51/0.70           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['65', '69'])).
% 0.51/0.70  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.51/0.70  thf('72', plain,
% 0.51/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('73', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.51/0.70  thf('75', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['26', '31'])).
% 0.51/0.70  thf('76', plain,
% 0.51/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('77', plain,
% 0.51/0.70      (![X9 : $i, X10 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X9)
% 0.51/0.70          | ~ (m1_pre_topc @ X10 @ 
% 0.51/0.70               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.51/0.70          | (m1_pre_topc @ X10 @ X9)
% 0.51/0.70          | ~ (l1_pre_topc @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.51/0.70  thf('78', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_pre_topc @ X0 @ sk_C)
% 0.51/0.70          | ~ (l1_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.51/0.70  thf('79', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('80', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_pre_topc @ X0 @ sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.51/0.70  thf('81', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['75', '80'])).
% 0.51/0.70  thf('82', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['81', '82'])).
% 0.51/0.70  thf('84', plain,
% 0.51/0.70      (![X19 : $i, X20 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X19 @ X20)
% 0.51/0.70          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.51/0.70          | ~ (l1_pre_topc @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.51/0.70  thf('85', plain,
% 0.51/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.51/0.70        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['83', '84'])).
% 0.51/0.70  thf('86', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('87', plain,
% 0.51/0.70      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.51/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.51/0.70      inference('demod', [status(thm)], ['85', '86'])).
% 0.51/0.70  thf('88', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | ((X18) != (u1_struct_0 @ X16))
% 0.51/0.70          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.51/0.70          | ~ (m1_pre_topc @ X16 @ X17)
% 0.51/0.70          | (v3_pre_topc @ X18 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (v2_pre_topc @ X17))),
% 0.51/0.70      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.51/0.70  thf('89', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i]:
% 0.51/0.70         (~ (v2_pre_topc @ X17)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.51/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.51/0.70          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.51/0.70          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.51/0.70      inference('simplify', [status(thm)], ['88'])).
% 0.51/0.70  thf('90', plain,
% 0.51/0.70      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 0.51/0.70        | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.51/0.70        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.51/0.70        | ~ (v2_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['87', '89'])).
% 0.51/0.70  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['81', '82'])).
% 0.51/0.70  thf('92', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['81', '82'])).
% 0.51/0.70  thf(fc10_tops_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.51/0.70  thf('93', plain,
% 0.51/0.70      (![X11 : $i]:
% 0.51/0.70         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.51/0.70          | ~ (l1_pre_topc @ X11)
% 0.51/0.70          | ~ (v2_pre_topc @ X11))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.51/0.70  thf(d3_struct_0, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.51/0.70  thf('94', plain,
% 0.51/0.70      (![X2 : $i]:
% 0.51/0.70         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.70  thf('95', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['56'])).
% 0.51/0.70  thf('96', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i]:
% 0.51/0.70         (~ (v2_pre_topc @ X17)
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.51/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | (v1_tsep_1 @ X16 @ X17)
% 0.51/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.51/0.70          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.51/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.70  thf('97', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.51/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.51/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (v2_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['95', '96'])).
% 0.51/0.70  thf('98', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (v2_pre_topc @ X0)
% 0.51/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.51/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['97'])).
% 0.51/0.70  thf('99', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.51/0.70          | ~ (l1_struct_0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.51/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.51/0.70          | ~ (v2_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['94', '98'])).
% 0.51/0.70  thf('100', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (v2_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (v2_pre_topc @ X0)
% 0.51/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_struct_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['93', '99'])).
% 0.51/0.70  thf('101', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_struct_0 @ X0)
% 0.51/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.51/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (v2_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['100'])).
% 0.51/0.70  thf('102', plain,
% 0.51/0.70      ((~ (v2_pre_topc @ sk_C)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.51/0.70        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.51/0.70        | ~ (l1_struct_0 @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['92', '101'])).
% 0.51/0.70  thf('103', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('104', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.70          | (v2_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X1)
% 0.51/0.70          | ~ (v2_pre_topc @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.51/0.70  thf('105', plain,
% 0.51/0.70      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['103', '104'])).
% 0.51/0.70  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('108', plain, ((v2_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.51/0.70  thf('109', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('110', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf(dt_l1_pre_topc, axiom,
% 0.51/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.70  thf('111', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.70  thf('112', plain, ((l1_struct_0 @ sk_C)),
% 0.51/0.70      inference('sup-', [status(thm)], ['110', '111'])).
% 0.51/0.70  thf('113', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['102', '108', '109', '112'])).
% 0.51/0.70  thf('114', plain, ((l1_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('115', plain, ((v2_pre_topc @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.51/0.70  thf('116', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['90', '91', '113', '114', '115'])).
% 0.51/0.70  thf('117', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['62', '63', '64', '74', '116'])).
% 0.51/0.70  thf('118', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['53', '117'])).
% 0.51/0.70  thf('119', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('120', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.51/0.70        | (v2_struct_0 @ sk_D)
% 0.51/0.70        | (v2_struct_0 @ sk_B))),
% 0.51/0.70      inference('demod', [status(thm)],
% 0.51/0.70                ['13', '14', '15', '16', '19', '20', '32', '118', '119'])).
% 0.51/0.70  thf('121', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('122', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_B)
% 0.51/0.70        | (v2_struct_0 @ sk_D)
% 0.51/0.70        | (v2_struct_0 @ sk_C)
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['120', '121'])).
% 0.51/0.70  thf('123', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('124', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['122', '123'])).
% 0.51/0.70  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('126', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.51/0.70      inference('clc', [status(thm)], ['124', '125'])).
% 0.51/0.70  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('128', plain, ((v2_struct_0 @ sk_C)),
% 0.51/0.70      inference('clc', [status(thm)], ['126', '127'])).
% 0.51/0.70  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
