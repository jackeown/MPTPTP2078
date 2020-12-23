%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jw0KBKZZ4X

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 372 expanded)
%              Number of leaves         :   59 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          : 1437 (9970 expanded)
%              Number of equality atoms :   14 ( 242 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( v2_struct_0 @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ( v2_struct_0 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X53 )
      | ~ ( v1_tsep_1 @ X54 @ X52 )
      | ~ ( m1_pre_topc @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ X52 ) )
      | ( X55 != X56 )
      | ~ ( r1_tmap_1 @ X54 @ X51 @ ( k3_tmap_1 @ X53 @ X51 @ X52 @ X54 @ X57 ) @ X56 )
      | ( r1_tmap_1 @ X52 @ X51 @ X57 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ X54 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X51 ) ) ) )
      | ~ ( v1_funct_2 @ X57 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X51 ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( m1_pre_topc @ X54 @ X53 )
      | ( v2_struct_0 @ X54 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X56: $i,X57: $i] :
      ( ( v2_struct_0 @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ( v2_struct_0 @ X54 )
      | ~ ( m1_pre_topc @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X51 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X52 ) @ ( u1_struct_0 @ X51 ) ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ X54 ) )
      | ( r1_tmap_1 @ X52 @ X51 @ X57 @ X56 )
      | ~ ( r1_tmap_1 @ X54 @ X51 @ ( k3_tmap_1 @ X53 @ X51 @ X52 @ X54 @ X57 ) @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ X52 ) )
      | ~ ( m1_pre_topc @ X54 @ X52 )
      | ~ ( v1_tsep_1 @ X54 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X53 )
      | ( v2_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
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
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('22',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( m1_pre_topc @ X34 @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( l1_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ ( g1_pre_topc @ ( u1_struct_0 @ X32 ) @ ( u1_pre_topc @ X32 ) ) )
      | ( m1_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( l1_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X46 @ X47 )
      | ( r1_tarski @ ( u1_struct_0 @ X46 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_tsep_1 @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X42 ) )
      | ( v1_tsep_1 @ X40 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['26','31'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ ( g1_pre_topc @ ( u1_struct_0 @ X32 ) @ ( u1_pre_topc @ X32 ) ) )
      | ( m1_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['54','59'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('61',plain,(
    ! [X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ( r2_hidden @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('62',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r2_hidden @ X27 @ ( u1_pre_topc @ X28 ) )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

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

thf('72',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( X39
       != ( u1_struct_0 @ X37 ) )
      | ~ ( v3_pre_topc @ X39 @ X38 )
      | ( v1_tsep_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('73',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v1_tsep_1 @ X37 @ X38 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X37 ) @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v1_tsep_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('80',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('82',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['78','79','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['54','59'])).

thf('88',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('89',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('90',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','32','94','95'])).

thf('97',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jw0KBKZZ4X
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.19/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.37  % Solved by: fo/fo7.sh
% 1.19/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.37  % done 1825 iterations in 0.907s
% 1.19/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.37  % SZS output start Refutation
% 1.19/1.37  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.19/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.37  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.19/1.37  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 1.19/1.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.19/1.37  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.19/1.37  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.37  thf(sk_E_type, type, sk_E: $i).
% 1.19/1.37  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.19/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.37  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 1.19/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.19/1.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.37  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.19/1.37  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.19/1.37  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.19/1.37  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.19/1.37  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.19/1.37  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.19/1.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.19/1.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.37  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.19/1.37  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 1.19/1.37  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.19/1.37  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.19/1.37  thf(sk_D_type, type, sk_D: $i).
% 1.19/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.19/1.37  thf(sk_G_type, type, sk_G: $i).
% 1.19/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.37  thf(sk_F_type, type, sk_F: $i).
% 1.19/1.37  thf(t88_tmap_1, conjecture,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.37             ( l1_pre_topc @ B ) ) =>
% 1.19/1.37           ( ![C:$i]:
% 1.19/1.37             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.37               ( ![D:$i]:
% 1.19/1.37                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.37                   ( ![E:$i]:
% 1.19/1.37                     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.37                         ( v1_funct_2 @
% 1.19/1.37                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.37                         ( m1_subset_1 @
% 1.19/1.37                           E @ 
% 1.19/1.37                           ( k1_zfmisc_1 @
% 1.19/1.37                             ( k2_zfmisc_1 @
% 1.19/1.37                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.37                       ( ( ( g1_pre_topc @
% 1.19/1.37                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.19/1.37                           ( D ) ) =>
% 1.19/1.37                         ( ![F:$i]:
% 1.19/1.37                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.19/1.37                             ( ![G:$i]:
% 1.19/1.37                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.19/1.37                                 ( ( ( ( F ) = ( G ) ) & 
% 1.19/1.37                                     ( r1_tmap_1 @
% 1.19/1.37                                       C @ B @ 
% 1.19/1.37                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.19/1.37                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.37    (~( ![A:$i]:
% 1.19/1.37        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.19/1.37            ( l1_pre_topc @ A ) ) =>
% 1.19/1.37          ( ![B:$i]:
% 1.19/1.37            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.37                ( l1_pre_topc @ B ) ) =>
% 1.19/1.37              ( ![C:$i]:
% 1.19/1.37                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.37                  ( ![D:$i]:
% 1.19/1.37                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.37                      ( ![E:$i]:
% 1.19/1.37                        ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.37                            ( v1_funct_2 @
% 1.19/1.37                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.37                            ( m1_subset_1 @
% 1.19/1.37                              E @ 
% 1.19/1.37                              ( k1_zfmisc_1 @
% 1.19/1.37                                ( k2_zfmisc_1 @
% 1.19/1.37                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.37                          ( ( ( g1_pre_topc @
% 1.19/1.37                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.19/1.37                              ( D ) ) =>
% 1.19/1.37                            ( ![F:$i]:
% 1.19/1.37                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.19/1.37                                ( ![G:$i]:
% 1.19/1.37                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.19/1.37                                    ( ( ( ( F ) = ( G ) ) & 
% 1.19/1.37                                        ( r1_tmap_1 @
% 1.19/1.37                                          C @ B @ 
% 1.19/1.37                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.19/1.37                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.19/1.37    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.19/1.37  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('1', plain,
% 1.19/1.37      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 1.19/1.37        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('2', plain, (((sk_F) = (sk_G))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('3', plain,
% 1.19/1.37      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 1.19/1.37        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 1.19/1.37      inference('demod', [status(thm)], ['1', '2'])).
% 1.19/1.37  thf('4', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_E @ 
% 1.19/1.37        (k1_zfmisc_1 @ 
% 1.19/1.37         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(t86_tmap_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.19/1.37             ( l1_pre_topc @ B ) ) =>
% 1.19/1.37           ( ![C:$i]:
% 1.19/1.37             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.37               ( ![D:$i]:
% 1.19/1.37                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.19/1.37                   ( ![E:$i]:
% 1.19/1.37                     ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.37                         ( v1_funct_2 @
% 1.19/1.37                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.19/1.37                         ( m1_subset_1 @
% 1.19/1.37                           E @ 
% 1.19/1.37                           ( k1_zfmisc_1 @
% 1.19/1.37                             ( k2_zfmisc_1 @
% 1.19/1.37                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.19/1.37                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.19/1.37                         ( ![F:$i]:
% 1.19/1.37                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.19/1.37                             ( ![G:$i]:
% 1.19/1.37                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.19/1.37                                 ( ( ( F ) = ( G ) ) =>
% 1.19/1.37                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.19/1.37                                     ( r1_tmap_1 @
% 1.19/1.37                                       C @ B @ 
% 1.19/1.37                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.37  thf('5', plain,
% 1.19/1.37      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 1.19/1.37         ((v2_struct_0 @ X51)
% 1.19/1.37          | ~ (v2_pre_topc @ X51)
% 1.19/1.37          | ~ (l1_pre_topc @ X51)
% 1.19/1.37          | (v2_struct_0 @ X52)
% 1.19/1.37          | ~ (m1_pre_topc @ X52 @ X53)
% 1.19/1.37          | ~ (v1_tsep_1 @ X54 @ X52)
% 1.19/1.37          | ~ (m1_pre_topc @ X54 @ X52)
% 1.19/1.37          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ X52))
% 1.19/1.37          | ((X55) != (X56))
% 1.19/1.37          | ~ (r1_tmap_1 @ X54 @ X51 @ 
% 1.19/1.37               (k3_tmap_1 @ X53 @ X51 @ X52 @ X54 @ X57) @ X56)
% 1.19/1.37          | (r1_tmap_1 @ X52 @ X51 @ X57 @ X55)
% 1.19/1.37          | ~ (m1_subset_1 @ X56 @ (u1_struct_0 @ X54))
% 1.19/1.37          | ~ (m1_subset_1 @ X57 @ 
% 1.19/1.37               (k1_zfmisc_1 @ 
% 1.19/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X51))))
% 1.19/1.37          | ~ (v1_funct_2 @ X57 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X51))
% 1.19/1.37          | ~ (v1_funct_1 @ X57)
% 1.19/1.37          | ~ (m1_pre_topc @ X54 @ X53)
% 1.19/1.37          | (v2_struct_0 @ X54)
% 1.19/1.37          | ~ (l1_pre_topc @ X53)
% 1.19/1.37          | ~ (v2_pre_topc @ X53)
% 1.19/1.37          | (v2_struct_0 @ X53))),
% 1.19/1.37      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.19/1.37  thf('6', plain,
% 1.19/1.37      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X56 : $i, X57 : $i]:
% 1.19/1.37         ((v2_struct_0 @ X53)
% 1.19/1.37          | ~ (v2_pre_topc @ X53)
% 1.19/1.37          | ~ (l1_pre_topc @ X53)
% 1.19/1.37          | (v2_struct_0 @ X54)
% 1.19/1.37          | ~ (m1_pre_topc @ X54 @ X53)
% 1.19/1.37          | ~ (v1_funct_1 @ X57)
% 1.19/1.37          | ~ (v1_funct_2 @ X57 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X51))
% 1.19/1.37          | ~ (m1_subset_1 @ X57 @ 
% 1.19/1.37               (k1_zfmisc_1 @ 
% 1.19/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X52) @ (u1_struct_0 @ X51))))
% 1.19/1.37          | ~ (m1_subset_1 @ X56 @ (u1_struct_0 @ X54))
% 1.19/1.37          | (r1_tmap_1 @ X52 @ X51 @ X57 @ X56)
% 1.19/1.37          | ~ (r1_tmap_1 @ X54 @ X51 @ 
% 1.19/1.37               (k3_tmap_1 @ X53 @ X51 @ X52 @ X54 @ X57) @ X56)
% 1.19/1.37          | ~ (m1_subset_1 @ X56 @ (u1_struct_0 @ X52))
% 1.19/1.37          | ~ (m1_pre_topc @ X54 @ X52)
% 1.19/1.37          | ~ (v1_tsep_1 @ X54 @ X52)
% 1.19/1.37          | ~ (m1_pre_topc @ X52 @ X53)
% 1.19/1.37          | (v2_struct_0 @ X52)
% 1.19/1.37          | ~ (l1_pre_topc @ X51)
% 1.19/1.37          | ~ (v2_pre_topc @ X51)
% 1.19/1.37          | (v2_struct_0 @ X51))),
% 1.19/1.37      inference('simplify', [status(thm)], ['5'])).
% 1.19/1.37  thf('7', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.37         ((v2_struct_0 @ sk_B_2)
% 1.19/1.37          | ~ (v2_pre_topc @ sk_B_2)
% 1.19/1.37          | ~ (l1_pre_topc @ sk_B_2)
% 1.19/1.37          | (v2_struct_0 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.19/1.37          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.19/1.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.19/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 1.19/1.37               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 1.19/1.37          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 1.19/1.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.19/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.19/1.37               (u1_struct_0 @ sk_B_2))
% 1.19/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.37          | ~ (m1_pre_topc @ X1 @ X0)
% 1.19/1.37          | (v2_struct_0 @ X1)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | (v2_struct_0 @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['4', '6'])).
% 1.19/1.37  thf('8', plain, ((v2_pre_topc @ sk_B_2)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('9', plain, ((l1_pre_topc @ sk_B_2)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('10', plain,
% 1.19/1.37      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('12', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.37         ((v2_struct_0 @ sk_B_2)
% 1.19/1.37          | (v2_struct_0 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.19/1.37          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.19/1.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.19/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 1.19/1.37               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 1.19/1.37          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 1.19/1.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.19/1.37          | ~ (m1_pre_topc @ X1 @ X0)
% 1.19/1.37          | (v2_struct_0 @ X1)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | (v2_struct_0 @ X0))),
% 1.19/1.37      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.19/1.37  thf('13', plain,
% 1.19/1.37      (((v2_struct_0 @ sk_A)
% 1.19/1.37        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.37        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.37        | (v2_struct_0 @ sk_C_1)
% 1.19/1.37        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 1.19/1.37        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 1.19/1.37        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 1.19/1.37        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.19/1.37        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.19/1.37        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.19/1.37        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.19/1.37        | (v2_struct_0 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_B_2))),
% 1.19/1.37      inference('sup-', [status(thm)], ['3', '12'])).
% 1.19/1.37  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('16', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('18', plain, (((sk_F) = (sk_G))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 1.19/1.37      inference('demod', [status(thm)], ['17', '18'])).
% 1.19/1.37  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('21', plain,
% 1.19/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.19/1.37         = (sk_D))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(t2_tsep_1, axiom,
% 1.19/1.37    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.19/1.37  thf('22', plain,
% 1.19/1.37      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 1.19/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.19/1.37  thf(t65_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( l1_pre_topc @ B ) =>
% 1.19/1.37           ( ( m1_pre_topc @ A @ B ) <=>
% 1.19/1.37             ( m1_pre_topc @
% 1.19/1.37               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.19/1.37  thf('23', plain,
% 1.19/1.37      (![X33 : $i, X34 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X33)
% 1.19/1.37          | ~ (m1_pre_topc @ X34 @ X33)
% 1.19/1.37          | (m1_pre_topc @ X34 @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)))
% 1.19/1.37          | ~ (l1_pre_topc @ X34))),
% 1.19/1.37      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.19/1.37  thf('24', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (m1_pre_topc @ X0 @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['22', '23'])).
% 1.19/1.37  thf('25', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((m1_pre_topc @ X0 @ 
% 1.19/1.37           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['24'])).
% 1.19/1.37  thf('26', plain,
% 1.19/1.37      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 1.19/1.37      inference('sup+', [status(thm)], ['21', '25'])).
% 1.19/1.37  thf('27', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(dt_m1_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.19/1.37  thf('28', plain,
% 1.19/1.37      (![X29 : $i, X30 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X29 @ X30)
% 1.19/1.37          | (l1_pre_topc @ X29)
% 1.19/1.37          | ~ (l1_pre_topc @ X30))),
% 1.19/1.37      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.19/1.37  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['27', '28'])).
% 1.19/1.37  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('31', plain, ((l1_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('32', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.19/1.37      inference('demod', [status(thm)], ['26', '31'])).
% 1.19/1.37  thf('33', plain,
% 1.19/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.19/1.37         = (sk_D))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('34', plain,
% 1.19/1.37      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 1.19/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.19/1.37  thf(t59_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( m1_pre_topc @
% 1.19/1.37             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 1.19/1.37           ( m1_pre_topc @ B @ A ) ) ) ))).
% 1.19/1.37  thf('35', plain,
% 1.19/1.37      (![X31 : $i, X32 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X31 @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X32) @ (u1_pre_topc @ X32)))
% 1.19/1.37          | (m1_pre_topc @ X31 @ X32)
% 1.19/1.37          | ~ (l1_pre_topc @ X32))),
% 1.19/1.37      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.19/1.37  thf('36', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (m1_pre_topc @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['34', '35'])).
% 1.19/1.37  thf('37', plain,
% 1.19/1.37      ((~ (l1_pre_topc @ sk_D)
% 1.19/1.37        | (m1_pre_topc @ 
% 1.19/1.37           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 1.19/1.37           sk_C_1)
% 1.19/1.37        | ~ (l1_pre_topc @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['33', '36'])).
% 1.19/1.37  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('39', plain,
% 1.19/1.37      (![X29 : $i, X30 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X29 @ X30)
% 1.19/1.37          | (l1_pre_topc @ X29)
% 1.19/1.37          | ~ (l1_pre_topc @ X30))),
% 1.19/1.37      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.19/1.37  thf('40', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.19/1.37      inference('sup-', [status(thm)], ['38', '39'])).
% 1.19/1.37  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('42', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.37      inference('demod', [status(thm)], ['40', '41'])).
% 1.19/1.37  thf('43', plain,
% 1.19/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.19/1.37         = (sk_D))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('44', plain, ((l1_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 1.19/1.37  thf('46', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.19/1.37      inference('demod', [status(thm)], ['26', '31'])).
% 1.19/1.37  thf(t35_borsuk_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( m1_pre_topc @ B @ A ) =>
% 1.19/1.37           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.19/1.37  thf('47', plain,
% 1.19/1.37      (![X46 : $i, X47 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X46 @ X47)
% 1.19/1.37          | (r1_tarski @ (u1_struct_0 @ X46) @ (u1_struct_0 @ X47))
% 1.19/1.37          | ~ (l1_pre_topc @ X47))),
% 1.19/1.37      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.19/1.37  thf('48', plain,
% 1.19/1.37      ((~ (l1_pre_topc @ sk_D)
% 1.19/1.37        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['46', '47'])).
% 1.19/1.37  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 1.19/1.37      inference('demod', [status(thm)], ['40', '41'])).
% 1.19/1.37  thf('50', plain,
% 1.19/1.37      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 1.19/1.37      inference('demod', [status(thm)], ['48', '49'])).
% 1.19/1.37  thf(t19_tsep_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.19/1.37           ( ![C:$i]:
% 1.19/1.37             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.19/1.37               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 1.19/1.37                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 1.19/1.37  thf('51', plain,
% 1.19/1.37      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.19/1.37         (~ (v1_tsep_1 @ X40 @ X41)
% 1.19/1.37          | ~ (m1_pre_topc @ X40 @ X41)
% 1.19/1.37          | ~ (r1_tarski @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X42))
% 1.19/1.37          | (v1_tsep_1 @ X40 @ X42)
% 1.19/1.37          | ~ (m1_pre_topc @ X42 @ X41)
% 1.19/1.37          | (v2_struct_0 @ X42)
% 1.19/1.37          | ~ (l1_pre_topc @ X41)
% 1.19/1.37          | ~ (v2_pre_topc @ X41)
% 1.19/1.37          | (v2_struct_0 @ X41))),
% 1.19/1.37      inference('cnf', [status(esa)], [t19_tsep_1])).
% 1.19/1.37  thf('52', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((v2_struct_0 @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (v2_struct_0 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.19/1.37          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.19/1.37          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 1.19/1.37          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['50', '51'])).
% 1.19/1.37  thf('53', plain,
% 1.19/1.37      ((~ (v1_tsep_1 @ sk_C_1 @ sk_C_1)
% 1.19/1.37        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 1.19/1.37        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_D)
% 1.19/1.37        | ~ (l1_pre_topc @ sk_C_1)
% 1.19/1.37        | ~ (v2_pre_topc @ sk_C_1)
% 1.19/1.37        | (v2_struct_0 @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['45', '52'])).
% 1.19/1.37  thf('54', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.19/1.37      inference('demod', [status(thm)], ['26', '31'])).
% 1.19/1.37  thf('55', plain,
% 1.19/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.19/1.37         = (sk_D))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('56', plain,
% 1.19/1.37      (![X31 : $i, X32 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X31 @ 
% 1.19/1.37             (g1_pre_topc @ (u1_struct_0 @ X32) @ (u1_pre_topc @ X32)))
% 1.19/1.37          | (m1_pre_topc @ X31 @ X32)
% 1.19/1.37          | ~ (l1_pre_topc @ X32))),
% 1.19/1.37      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.19/1.37  thf('57', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.19/1.37          | ~ (l1_pre_topc @ sk_C_1)
% 1.19/1.37          | (m1_pre_topc @ X0 @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['55', '56'])).
% 1.19/1.37  thf('58', plain, ((l1_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('59', plain,
% 1.19/1.37      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C_1))),
% 1.19/1.37      inference('demod', [status(thm)], ['57', '58'])).
% 1.19/1.37  thf('60', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.19/1.37      inference('sup-', [status(thm)], ['54', '59'])).
% 1.19/1.37  thf(d1_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ( v2_pre_topc @ A ) <=>
% 1.19/1.37         ( ( ![B:$i]:
% 1.19/1.37             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37               ( ![C:$i]:
% 1.19/1.37                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 1.19/1.37                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 1.19/1.37                     ( r2_hidden @
% 1.19/1.37                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 1.19/1.37                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 1.19/1.37           ( ![B:$i]:
% 1.19/1.37             ( ( m1_subset_1 @
% 1.19/1.37                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.37               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 1.19/1.37                 ( r2_hidden @
% 1.19/1.37                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.19/1.37                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 1.19/1.37           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_2, axiom,
% 1.19/1.37    (![B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_5 @ B @ A ) <=>
% 1.19/1.37       ( ( m1_subset_1 @
% 1.19/1.37           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.37         ( zip_tseitin_4 @ B @ A ) ) ))).
% 1.19/1.37  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_4, axiom,
% 1.19/1.37    (![B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_4 @ B @ A ) <=>
% 1.19/1.37       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 1.19/1.37         ( r2_hidden @
% 1.19/1.37           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_6, axiom,
% 1.19/1.37    (![B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_3 @ B @ A ) <=>
% 1.19/1.37       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_8, axiom,
% 1.19/1.37    (![C:$i,B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 1.19/1.37       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 1.19/1.37  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_10, axiom,
% 1.19/1.37    (![C:$i,B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 1.19/1.37       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 1.19/1.37         ( r2_hidden @
% 1.19/1.37           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.19/1.37  thf(zf_stmt_12, axiom,
% 1.19/1.37    (![C:$i,B:$i,A:$i]:
% 1.19/1.37     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 1.19/1.37       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 1.19/1.37         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_13, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ( v2_pre_topc @ A ) <=>
% 1.19/1.37         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 1.19/1.37           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 1.19/1.37           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 1.19/1.37  thf('61', plain,
% 1.19/1.37      (![X24 : $i]:
% 1.19/1.37         (~ (v2_pre_topc @ X24)
% 1.19/1.37          | (r2_hidden @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24))
% 1.19/1.37          | ~ (l1_pre_topc @ X24))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_13])).
% 1.19/1.37  thf('62', plain,
% 1.19/1.37      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 1.19/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.19/1.37  thf(t1_tsep_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( m1_pre_topc @ B @ A ) =>
% 1.19/1.37           ( m1_subset_1 @
% 1.19/1.37             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('63', plain,
% 1.19/1.37      (![X43 : $i, X44 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X43 @ X44)
% 1.19/1.37          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 1.19/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.19/1.37          | ~ (l1_pre_topc @ X44))),
% 1.19/1.37      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.19/1.37  thf('64', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.19/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['62', '63'])).
% 1.19/1.37  thf('65', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.19/1.37           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['64'])).
% 1.19/1.37  thf(d5_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( l1_pre_topc @ A ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37           ( ( v3_pre_topc @ B @ A ) <=>
% 1.19/1.37             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 1.19/1.37  thf('66', plain,
% 1.19/1.37      (![X27 : $i, X28 : $i]:
% 1.19/1.37         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.19/1.37          | ~ (r2_hidden @ X27 @ (u1_pre_topc @ X28))
% 1.19/1.37          | (v3_pre_topc @ X27 @ X28)
% 1.19/1.37          | ~ (l1_pre_topc @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.19/1.37  thf('67', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.19/1.37          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['65', '66'])).
% 1.19/1.37  thf('68', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.19/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['67'])).
% 1.19/1.37  thf('69', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['61', '68'])).
% 1.19/1.37  thf('70', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['69'])).
% 1.19/1.37  thf('71', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.19/1.37           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['64'])).
% 1.19/1.37  thf(t16_tsep_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.37       ( ![B:$i]:
% 1.19/1.37         ( ( m1_pre_topc @ B @ A ) =>
% 1.19/1.37           ( ![C:$i]:
% 1.19/1.37             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.37               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.19/1.37                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.19/1.37                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.19/1.37  thf('72', plain,
% 1.19/1.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X37 @ X38)
% 1.19/1.37          | ((X39) != (u1_struct_0 @ X37))
% 1.19/1.37          | ~ (v3_pre_topc @ X39 @ X38)
% 1.19/1.37          | (v1_tsep_1 @ X37 @ X38)
% 1.19/1.37          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.19/1.37          | ~ (l1_pre_topc @ X38)
% 1.19/1.37          | ~ (v2_pre_topc @ X38))),
% 1.19/1.37      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.19/1.37  thf('73', plain,
% 1.19/1.37      (![X37 : $i, X38 : $i]:
% 1.19/1.37         (~ (v2_pre_topc @ X38)
% 1.19/1.37          | ~ (l1_pre_topc @ X38)
% 1.19/1.37          | ~ (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 1.19/1.37               (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.19/1.37          | (v1_tsep_1 @ X37 @ X38)
% 1.19/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X37) @ X38)
% 1.19/1.37          | ~ (m1_pre_topc @ X37 @ X38))),
% 1.19/1.37      inference('simplify', [status(thm)], ['72'])).
% 1.19/1.37  thf('74', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (m1_pre_topc @ X0 @ X0)
% 1.19/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.19/1.37          | (v1_tsep_1 @ X0 @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['71', '73'])).
% 1.19/1.37  thf('75', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (v2_pre_topc @ X0)
% 1.19/1.37          | (v1_tsep_1 @ X0 @ X0)
% 1.19/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.19/1.37          | ~ (m1_pre_topc @ X0 @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['74'])).
% 1.19/1.37  thf('76', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0)
% 1.19/1.37          | ~ (m1_pre_topc @ X0 @ X0)
% 1.19/1.37          | (v1_tsep_1 @ X0 @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['70', '75'])).
% 1.19/1.37  thf('77', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((v1_tsep_1 @ X0 @ X0)
% 1.19/1.37          | ~ (m1_pre_topc @ X0 @ X0)
% 1.19/1.37          | ~ (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X0))),
% 1.19/1.37      inference('simplify', [status(thm)], ['76'])).
% 1.19/1.37  thf('78', plain,
% 1.19/1.37      ((~ (l1_pre_topc @ sk_C_1)
% 1.19/1.37        | ~ (v2_pre_topc @ sk_C_1)
% 1.19/1.37        | (v1_tsep_1 @ sk_C_1 @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['60', '77'])).
% 1.19/1.37  thf('79', plain, ((l1_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('80', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(cc1_pre_topc, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.37       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.19/1.37  thf('81', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         (~ (m1_pre_topc @ X0 @ X1)
% 1.19/1.37          | (v2_pre_topc @ X0)
% 1.19/1.37          | ~ (l1_pre_topc @ X1)
% 1.19/1.37          | ~ (v2_pre_topc @ X1))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.19/1.37  thf('82', plain,
% 1.19/1.37      ((~ (v2_pre_topc @ sk_A)
% 1.19/1.37        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.37        | (v2_pre_topc @ sk_C_1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['80', '81'])).
% 1.19/1.37  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('85', plain, ((v2_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.19/1.37  thf('86', plain, ((v1_tsep_1 @ sk_C_1 @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['78', '79', '85'])).
% 1.19/1.37  thf('87', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 1.19/1.37      inference('sup-', [status(thm)], ['54', '59'])).
% 1.19/1.37  thf('88', plain, ((l1_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('89', plain, ((v2_pre_topc @ sk_C_1)),
% 1.19/1.37      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.19/1.37  thf('90', plain,
% 1.19/1.37      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_C_1))),
% 1.19/1.37      inference('demod', [status(thm)], ['53', '86', '87', '88', '89'])).
% 1.19/1.37  thf('91', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('92', plain, (((v2_struct_0 @ sk_C_1) | (v1_tsep_1 @ sk_C_1 @ sk_D))),
% 1.19/1.37      inference('clc', [status(thm)], ['90', '91'])).
% 1.19/1.37  thf('93', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('94', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 1.19/1.37      inference('clc', [status(thm)], ['92', '93'])).
% 1.19/1.37  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('96', plain,
% 1.19/1.37      (((v2_struct_0 @ sk_A)
% 1.19/1.37        | (v2_struct_0 @ sk_C_1)
% 1.19/1.37        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 1.19/1.37        | (v2_struct_0 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_B_2))),
% 1.19/1.37      inference('demod', [status(thm)],
% 1.19/1.37                ['13', '14', '15', '16', '19', '20', '32', '94', '95'])).
% 1.19/1.37  thf('97', plain, (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('98', plain,
% 1.19/1.37      (((v2_struct_0 @ sk_B_2)
% 1.19/1.37        | (v2_struct_0 @ sk_D)
% 1.19/1.37        | (v2_struct_0 @ sk_C_1)
% 1.19/1.37        | (v2_struct_0 @ sk_A))),
% 1.19/1.37      inference('sup-', [status(thm)], ['96', '97'])).
% 1.19/1.37  thf('99', plain, (~ (v2_struct_0 @ sk_D)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('100', plain,
% 1.19/1.37      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B_2))),
% 1.19/1.37      inference('sup-', [status(thm)], ['98', '99'])).
% 1.19/1.37  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('102', plain, (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_C_1))),
% 1.19/1.37      inference('clc', [status(thm)], ['100', '101'])).
% 1.19/1.37  thf('103', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('104', plain, ((v2_struct_0 @ sk_C_1)),
% 1.19/1.37      inference('clc', [status(thm)], ['102', '103'])).
% 1.19/1.37  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 1.19/1.37  
% 1.19/1.37  % SZS output end Refutation
% 1.19/1.37  
% 1.19/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
