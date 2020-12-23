%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fs28SWyCqw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:28 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 782 expanded)
%              Number of leaves         :   61 ( 257 expanded)
%              Depth                    :   31
%              Number of atoms          : 1899 (21974 expanded)
%              Number of equality atoms :   38 ( 648 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

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

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X32 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( ( g1_pre_topc @ X36 @ X37 )
       != ( g1_pre_topc @ X34 @ X35 ) )
      | ( X36 = X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X33: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('15',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

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

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ( v2_struct_0 @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( v1_tsep_1 @ X52 @ X50 )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ X50 ) )
      | ( X53 != X54 )
      | ~ ( r1_tmap_1 @ X52 @ X49 @ ( k3_tmap_1 @ X51 @ X49 @ X50 @ X52 @ X55 ) @ X54 )
      | ( r1_tmap_1 @ X50 @ X49 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ X52 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( v1_funct_2 @ X55 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_pre_topc @ X52 @ X51 )
      | ( v2_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('35',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X54: $i,X55: $i] :
      ( ( v2_struct_0 @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ( v2_struct_0 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X50 ) @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ X52 ) )
      | ( r1_tmap_1 @ X50 @ X49 @ X55 @ X54 )
      | ~ ( r1_tmap_1 @ X52 @ X49 @ ( k3_tmap_1 @ X51 @ X49 @ X50 @ X52 @ X55 ) @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_pre_topc @ X52 @ X50 )
      | ~ ( v1_tsep_1 @ X52 @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ( v2_struct_0 @ X50 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('44',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['40','41','44','45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('50',plain,(
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

thf('51',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

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

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( X42
       != ( u1_struct_0 @ X40 ) )
      | ~ ( v3_pre_topc @ X42 @ X41 )
      | ( v1_tsep_1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('56',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v1_tsep_1 @ X40 @ X41 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X40 ) @ X41 )
      | ~ ( m1_pre_topc @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('60',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('61',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','64'])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['53','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('68',plain,(
    ! [X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ( r2_hidden @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_pre_topc @ X39 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('81',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_pre_topc @ X39 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('88',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('91',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('94',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('98',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('100',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('102',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) @ sk_D ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_pre_topc @ sk_D @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['69','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('105',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('106',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('110',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('114',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['68','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('117',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('118',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','23','24','29','30'])).

thf('120',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('123',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( m1_pre_topc @ X39 @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['121','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('128',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['66','67','120','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['126','127'])).

thf('131',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('135',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','129','130','133','134','135','136','137'])).

thf('139',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['0','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fs28SWyCqw
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.01/3.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.01/3.25  % Solved by: fo/fo7.sh
% 3.01/3.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.01/3.25  % done 4314 iterations in 2.790s
% 3.01/3.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.01/3.25  % SZS output start Refutation
% 3.01/3.25  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 3.01/3.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.01/3.25  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.01/3.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.01/3.25  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.01/3.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.01/3.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.01/3.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.01/3.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 3.01/3.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.01/3.25  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.01/3.25  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 3.01/3.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.01/3.25  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 3.01/3.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.01/3.25  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 3.01/3.25  thf(sk_E_type, type, sk_E: $i).
% 3.01/3.25  thf(sk_D_type, type, sk_D: $i).
% 3.01/3.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.01/3.25  thf(sk_A_type, type, sk_A: $i).
% 3.01/3.25  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.01/3.25  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 3.01/3.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.01/3.25  thf(sk_F_type, type, sk_F: $i).
% 3.01/3.25  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.01/3.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.01/3.25  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 3.01/3.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.01/3.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.01/3.25  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 3.01/3.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.01/3.25  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 3.01/3.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.01/3.25  thf(sk_G_type, type, sk_G: $i).
% 3.01/3.25  thf(t88_tmap_1, conjecture,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.01/3.25             ( l1_pre_topc @ B ) ) =>
% 3.01/3.25           ( ![C:$i]:
% 3.01/3.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.01/3.25               ( ![D:$i]:
% 3.01/3.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.01/3.25                   ( ![E:$i]:
% 3.01/3.25                     ( ( ( v1_funct_1 @ E ) & 
% 3.01/3.25                         ( v1_funct_2 @
% 3.01/3.25                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.01/3.25                         ( m1_subset_1 @
% 3.01/3.25                           E @ 
% 3.01/3.25                           ( k1_zfmisc_1 @
% 3.01/3.25                             ( k2_zfmisc_1 @
% 3.01/3.25                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.01/3.25                       ( ( ( g1_pre_topc @
% 3.01/3.25                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.01/3.25                           ( D ) ) =>
% 3.01/3.25                         ( ![F:$i]:
% 3.01/3.25                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.01/3.25                             ( ![G:$i]:
% 3.01/3.25                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.01/3.25                                 ( ( ( ( F ) = ( G ) ) & 
% 3.01/3.25                                     ( r1_tmap_1 @
% 3.01/3.25                                       C @ B @ 
% 3.01/3.25                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 3.01/3.25                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_0, negated_conjecture,
% 3.01/3.25    (~( ![A:$i]:
% 3.01/3.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.01/3.25            ( l1_pre_topc @ A ) ) =>
% 3.01/3.25          ( ![B:$i]:
% 3.01/3.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.01/3.25                ( l1_pre_topc @ B ) ) =>
% 3.01/3.25              ( ![C:$i]:
% 3.01/3.25                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.01/3.25                  ( ![D:$i]:
% 3.01/3.25                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.01/3.25                      ( ![E:$i]:
% 3.01/3.25                        ( ( ( v1_funct_1 @ E ) & 
% 3.01/3.25                            ( v1_funct_2 @
% 3.01/3.25                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.01/3.25                            ( m1_subset_1 @
% 3.01/3.25                              E @ 
% 3.01/3.25                              ( k1_zfmisc_1 @
% 3.01/3.25                                ( k2_zfmisc_1 @
% 3.01/3.25                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.01/3.25                          ( ( ( g1_pre_topc @
% 3.01/3.25                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 3.01/3.25                              ( D ) ) =>
% 3.01/3.25                            ( ![F:$i]:
% 3.01/3.25                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.01/3.25                                ( ![G:$i]:
% 3.01/3.25                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.01/3.25                                    ( ( ( ( F ) = ( G ) ) & 
% 3.01/3.25                                        ( r1_tmap_1 @
% 3.01/3.25                                          C @ B @ 
% 3.01/3.25                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 3.01/3.25                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.01/3.25    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 3.01/3.25  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('1', plain,
% 3.01/3.25      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 3.01/3.25        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('2', plain, (((sk_F) = (sk_G))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('3', plain,
% 3.01/3.25      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 3.01/3.25        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 3.01/3.25      inference('demod', [status(thm)], ['1', '2'])).
% 3.01/3.25  thf('4', plain,
% 3.01/3.25      ((m1_subset_1 @ sk_E @ 
% 3.01/3.25        (k1_zfmisc_1 @ 
% 3.01/3.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('5', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf(abstractness_v1_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ( v1_pre_topc @ A ) =>
% 3.01/3.25         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 3.01/3.25  thf('6', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (v1_pre_topc @ X0)
% 3.01/3.25          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 3.01/3.25  thf(dt_u1_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( m1_subset_1 @
% 3.01/3.25         ( u1_pre_topc @ A ) @ 
% 3.01/3.25         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 3.01/3.25  thf('7', plain,
% 3.01/3.25      (![X32 : $i]:
% 3.01/3.25         ((m1_subset_1 @ (u1_pre_topc @ X32) @ 
% 3.01/3.25           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))
% 3.01/3.25          | ~ (l1_pre_topc @ X32))),
% 3.01/3.25      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 3.01/3.25  thf(free_g1_pre_topc, axiom,
% 3.01/3.25    (![A:$i,B:$i]:
% 3.01/3.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.01/3.25       ( ![C:$i,D:$i]:
% 3.01/3.25         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 3.01/3.25           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 3.01/3.25  thf('8', plain,
% 3.01/3.25      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.01/3.25         (((g1_pre_topc @ X36 @ X37) != (g1_pre_topc @ X34 @ X35))
% 3.01/3.25          | ((X36) = (X34))
% 3.01/3.25          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X36))))),
% 3.01/3.25      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 3.01/3.25  thf('9', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | ((u1_struct_0 @ X0) = (X1))
% 3.01/3.25          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 3.01/3.25              != (g1_pre_topc @ X1 @ X2)))),
% 3.01/3.25      inference('sup-', [status(thm)], ['7', '8'])).
% 3.01/3.25  thf('10', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.25         (((X0) != (g1_pre_topc @ X2 @ X1))
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | ((u1_struct_0 @ X0) = (X2))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('sup-', [status(thm)], ['6', '9'])).
% 3.01/3.25  thf('11', plain,
% 3.01/3.25      (![X1 : $i, X2 : $i]:
% 3.01/3.25         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 3.01/3.25          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 3.01/3.25          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 3.01/3.25      inference('simplify', [status(thm)], ['10'])).
% 3.01/3.25  thf('12', plain,
% 3.01/3.25      ((~ (v1_pre_topc @ sk_D)
% 3.01/3.25        | ~ (l1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 3.01/3.25        | ((u1_struct_0 @ 
% 3.01/3.25            (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 3.01/3.25            = (u1_struct_0 @ sk_C_1)))),
% 3.01/3.25      inference('sup-', [status(thm)], ['5', '11'])).
% 3.01/3.25  thf('13', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf(fc7_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 3.01/3.25       ( ( ~( v2_struct_0 @
% 3.01/3.25              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 3.01/3.25         ( v1_pre_topc @
% 3.01/3.25           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 3.01/3.25  thf('14', plain,
% 3.01/3.25      (![X33 : $i]:
% 3.01/3.25         ((v1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)))
% 3.01/3.25          | ~ (l1_pre_topc @ X33)
% 3.01/3.25          | (v2_struct_0 @ X33))),
% 3.01/3.25      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 3.01/3.25  thf('15', plain,
% 3.01/3.25      (((v1_pre_topc @ sk_D)
% 3.01/3.25        | (v2_struct_0 @ sk_C_1)
% 3.01/3.25        | ~ (l1_pre_topc @ sk_C_1))),
% 3.01/3.25      inference('sup+', [status(thm)], ['13', '14'])).
% 3.01/3.25  thf('16', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf(dt_m1_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.01/3.25  thf('17', plain,
% 3.01/3.25      (![X30 : $i, X31 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X30 @ X31)
% 3.01/3.25          | (l1_pre_topc @ X30)
% 3.01/3.25          | ~ (l1_pre_topc @ X31))),
% 3.01/3.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.01/3.25  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 3.01/3.25      inference('sup-', [status(thm)], ['16', '17'])).
% 3.01/3.25  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('20', plain, ((l1_pre_topc @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['18', '19'])).
% 3.01/3.25  thf('21', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['15', '20'])).
% 3.01/3.25  thf('22', plain, (~ (v2_struct_0 @ sk_C_1)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('23', plain, ((v1_pre_topc @ sk_D)),
% 3.01/3.25      inference('clc', [status(thm)], ['21', '22'])).
% 3.01/3.25  thf('24', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('26', plain,
% 3.01/3.25      (![X30 : $i, X31 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X30 @ X31)
% 3.01/3.25          | (l1_pre_topc @ X30)
% 3.01/3.25          | ~ (l1_pre_topc @ X31))),
% 3.01/3.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.01/3.25  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['25', '26'])).
% 3.01/3.25  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('30', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('31', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf('32', plain,
% 3.01/3.25      ((m1_subset_1 @ sk_E @ 
% 3.01/3.25        (k1_zfmisc_1 @ 
% 3.01/3.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 3.01/3.25      inference('demod', [status(thm)], ['4', '31'])).
% 3.01/3.25  thf('33', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf(t86_tmap_1, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.01/3.25             ( l1_pre_topc @ B ) ) =>
% 3.01/3.25           ( ![C:$i]:
% 3.01/3.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.01/3.25               ( ![D:$i]:
% 3.01/3.25                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.01/3.25                   ( ![E:$i]:
% 3.01/3.25                     ( ( ( v1_funct_1 @ E ) & 
% 3.01/3.25                         ( v1_funct_2 @
% 3.01/3.25                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.01/3.25                         ( m1_subset_1 @
% 3.01/3.25                           E @ 
% 3.01/3.25                           ( k1_zfmisc_1 @
% 3.01/3.25                             ( k2_zfmisc_1 @
% 3.01/3.25                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.01/3.25                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 3.01/3.25                         ( ![F:$i]:
% 3.01/3.25                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 3.01/3.25                             ( ![G:$i]:
% 3.01/3.25                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 3.01/3.25                                 ( ( ( F ) = ( G ) ) =>
% 3.01/3.25                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 3.01/3.25                                     ( r1_tmap_1 @
% 3.01/3.25                                       C @ B @ 
% 3.01/3.25                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.01/3.25  thf('34', plain,
% 3.01/3.25      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 3.01/3.25         ((v2_struct_0 @ X49)
% 3.01/3.25          | ~ (v2_pre_topc @ X49)
% 3.01/3.25          | ~ (l1_pre_topc @ X49)
% 3.01/3.25          | (v2_struct_0 @ X50)
% 3.01/3.25          | ~ (m1_pre_topc @ X50 @ X51)
% 3.01/3.25          | ~ (v1_tsep_1 @ X52 @ X50)
% 3.01/3.25          | ~ (m1_pre_topc @ X52 @ X50)
% 3.01/3.25          | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ X50))
% 3.01/3.25          | ((X53) != (X54))
% 3.01/3.25          | ~ (r1_tmap_1 @ X52 @ X49 @ 
% 3.01/3.25               (k3_tmap_1 @ X51 @ X49 @ X50 @ X52 @ X55) @ X54)
% 3.01/3.25          | (r1_tmap_1 @ X50 @ X49 @ X55 @ X53)
% 3.01/3.25          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ X52))
% 3.01/3.25          | ~ (m1_subset_1 @ X55 @ 
% 3.01/3.25               (k1_zfmisc_1 @ 
% 3.01/3.25                (k2_zfmisc_1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))))
% 3.01/3.25          | ~ (v1_funct_2 @ X55 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))
% 3.01/3.25          | ~ (v1_funct_1 @ X55)
% 3.01/3.25          | ~ (m1_pre_topc @ X52 @ X51)
% 3.01/3.25          | (v2_struct_0 @ X52)
% 3.01/3.25          | ~ (l1_pre_topc @ X51)
% 3.01/3.25          | ~ (v2_pre_topc @ X51)
% 3.01/3.25          | (v2_struct_0 @ X51))),
% 3.01/3.25      inference('cnf', [status(esa)], [t86_tmap_1])).
% 3.01/3.25  thf('35', plain,
% 3.01/3.25      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X54 : $i, X55 : $i]:
% 3.01/3.25         ((v2_struct_0 @ X51)
% 3.01/3.25          | ~ (v2_pre_topc @ X51)
% 3.01/3.25          | ~ (l1_pre_topc @ X51)
% 3.01/3.25          | (v2_struct_0 @ X52)
% 3.01/3.25          | ~ (m1_pre_topc @ X52 @ X51)
% 3.01/3.25          | ~ (v1_funct_1 @ X55)
% 3.01/3.25          | ~ (v1_funct_2 @ X55 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))
% 3.01/3.25          | ~ (m1_subset_1 @ X55 @ 
% 3.01/3.25               (k1_zfmisc_1 @ 
% 3.01/3.25                (k2_zfmisc_1 @ (u1_struct_0 @ X50) @ (u1_struct_0 @ X49))))
% 3.01/3.25          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ X52))
% 3.01/3.25          | (r1_tmap_1 @ X50 @ X49 @ X55 @ X54)
% 3.01/3.25          | ~ (r1_tmap_1 @ X52 @ X49 @ 
% 3.01/3.25               (k3_tmap_1 @ X51 @ X49 @ X50 @ X52 @ X55) @ X54)
% 3.01/3.25          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ X50))
% 3.01/3.25          | ~ (m1_pre_topc @ X52 @ X50)
% 3.01/3.25          | ~ (v1_tsep_1 @ X52 @ X50)
% 3.01/3.25          | ~ (m1_pre_topc @ X50 @ X51)
% 3.01/3.25          | (v2_struct_0 @ X50)
% 3.01/3.25          | ~ (l1_pre_topc @ X49)
% 3.01/3.25          | ~ (v2_pre_topc @ X49)
% 3.01/3.25          | (v2_struct_0 @ X49))),
% 3.01/3.25      inference('simplify', [status(thm)], ['34'])).
% 3.01/3.25  thf('36', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.01/3.25         (~ (m1_subset_1 @ X1 @ 
% 3.01/3.25             (k1_zfmisc_1 @ 
% 3.01/3.25              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 3.01/3.25          | (v2_struct_0 @ X0)
% 3.01/3.25          | ~ (v2_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (v2_struct_0 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ sk_D @ X2)
% 3.01/3.25          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ X3 @ sk_D)
% 3.01/3.25          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 3.01/3.25          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 3.01/3.25               X4)
% 3.01/3.25          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 3.01/3.25          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 3.01/3.25          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 3.01/3.25          | ~ (v1_funct_1 @ X1)
% 3.01/3.25          | ~ (m1_pre_topc @ X3 @ X2)
% 3.01/3.25          | (v2_struct_0 @ X3)
% 3.01/3.25          | ~ (l1_pre_topc @ X2)
% 3.01/3.25          | ~ (v2_pre_topc @ X2)
% 3.01/3.25          | (v2_struct_0 @ X2))),
% 3.01/3.25      inference('sup-', [status(thm)], ['33', '35'])).
% 3.01/3.25  thf('37', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf('38', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf('39', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.01/3.25         (~ (m1_subset_1 @ X1 @ 
% 3.01/3.25             (k1_zfmisc_1 @ 
% 3.01/3.25              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 3.01/3.25          | (v2_struct_0 @ X0)
% 3.01/3.25          | ~ (v2_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (v2_struct_0 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ sk_D @ X2)
% 3.01/3.25          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ X3 @ sk_D)
% 3.01/3.25          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_C_1))
% 3.01/3.25          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 3.01/3.25               X4)
% 3.01/3.25          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 3.01/3.25          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 3.01/3.25          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 3.01/3.25          | ~ (v1_funct_1 @ X1)
% 3.01/3.25          | ~ (m1_pre_topc @ X3 @ X2)
% 3.01/3.25          | (v2_struct_0 @ X3)
% 3.01/3.25          | ~ (l1_pre_topc @ X2)
% 3.01/3.25          | ~ (v2_pre_topc @ X2)
% 3.01/3.25          | (v2_struct_0 @ X2))),
% 3.01/3.25      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.01/3.25  thf('40', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.25         ((v2_struct_0 @ X0)
% 3.01/3.25          | ~ (v2_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (v2_struct_0 @ X1)
% 3.01/3.25          | ~ (m1_pre_topc @ X1 @ X0)
% 3.01/3.25          | ~ (v1_funct_1 @ sk_E)
% 3.01/3.25          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 3.01/3.25               (u1_struct_0 @ sk_B_2))
% 3.01/3.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 3.01/3.25          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 3.01/3.25          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 3.01/3.25               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 3.01/3.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 3.01/3.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.01/3.25          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.01/3.25          | (v2_struct_0 @ sk_D)
% 3.01/3.25          | ~ (l1_pre_topc @ sk_B_2)
% 3.01/3.25          | ~ (v2_pre_topc @ sk_B_2)
% 3.01/3.25          | (v2_struct_0 @ sk_B_2))),
% 3.01/3.25      inference('sup-', [status(thm)], ['32', '39'])).
% 3.01/3.25  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('42', plain,
% 3.01/3.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('43', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf('44', plain,
% 3.01/3.25      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 3.01/3.25      inference('demod', [status(thm)], ['42', '43'])).
% 3.01/3.25  thf('45', plain, ((l1_pre_topc @ sk_B_2)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('46', plain, ((v2_pre_topc @ sk_B_2)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('47', plain,
% 3.01/3.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.01/3.25         ((v2_struct_0 @ X0)
% 3.01/3.25          | ~ (v2_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (v2_struct_0 @ X1)
% 3.01/3.25          | ~ (m1_pre_topc @ X1 @ X0)
% 3.01/3.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 3.01/3.25          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 3.01/3.25          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 3.01/3.25               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 3.01/3.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 3.01/3.25          | ~ (m1_pre_topc @ X1 @ sk_D)
% 3.01/3.25          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 3.01/3.25          | ~ (m1_pre_topc @ sk_D @ X0)
% 3.01/3.25          | (v2_struct_0 @ sk_D)
% 3.01/3.25          | (v2_struct_0 @ sk_B_2))),
% 3.01/3.25      inference('demod', [status(thm)], ['40', '41', '44', '45', '46'])).
% 3.01/3.25  thf('48', plain,
% 3.01/3.25      (((v2_struct_0 @ sk_B_2)
% 3.01/3.25        | (v2_struct_0 @ sk_D)
% 3.01/3.25        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 3.01/3.25        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 3.01/3.25        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 3.01/3.25        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 3.01/3.25        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 3.01/3.25        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 3.01/3.25        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 3.01/3.25        | (v2_struct_0 @ sk_C_1)
% 3.01/3.25        | ~ (l1_pre_topc @ sk_A)
% 3.01/3.25        | ~ (v2_pre_topc @ sk_A)
% 3.01/3.25        | (v2_struct_0 @ sk_A))),
% 3.01/3.25      inference('sup-', [status(thm)], ['3', '47'])).
% 3.01/3.25  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf(t2_tsep_1, axiom,
% 3.01/3.25    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 3.01/3.25  thf('50', plain,
% 3.01/3.25      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 3.01/3.25      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.01/3.25  thf(t1_tsep_1, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( m1_pre_topc @ B @ A ) =>
% 3.01/3.25           ( m1_subset_1 @
% 3.01/3.25             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.01/3.25  thf('51', plain,
% 3.01/3.25      (![X43 : $i, X44 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X43 @ X44)
% 3.01/3.25          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 3.01/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 3.01/3.25          | ~ (l1_pre_topc @ X44))),
% 3.01/3.25      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.01/3.25  thf('52', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.01/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.01/3.25      inference('sup-', [status(thm)], ['50', '51'])).
% 3.01/3.25  thf('53', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.01/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('simplify', [status(thm)], ['52'])).
% 3.01/3.25  thf('54', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf(t16_tsep_1, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( m1_pre_topc @ B @ A ) =>
% 3.01/3.25           ( ![C:$i]:
% 3.01/3.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 3.01/3.25                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 3.01/3.25                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.01/3.25  thf('55', plain,
% 3.01/3.25      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X40 @ X41)
% 3.01/3.25          | ((X42) != (u1_struct_0 @ X40))
% 3.01/3.25          | ~ (v3_pre_topc @ X42 @ X41)
% 3.01/3.25          | (v1_tsep_1 @ X40 @ X41)
% 3.01/3.25          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 3.01/3.25          | ~ (l1_pre_topc @ X41)
% 3.01/3.25          | ~ (v2_pre_topc @ X41))),
% 3.01/3.25      inference('cnf', [status(esa)], [t16_tsep_1])).
% 3.01/3.25  thf('56', plain,
% 3.01/3.25      (![X40 : $i, X41 : $i]:
% 3.01/3.25         (~ (v2_pre_topc @ X41)
% 3.01/3.25          | ~ (l1_pre_topc @ X41)
% 3.01/3.25          | ~ (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 3.01/3.25               (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 3.01/3.25          | (v1_tsep_1 @ X40 @ X41)
% 3.01/3.25          | ~ (v3_pre_topc @ (u1_struct_0 @ X40) @ X41)
% 3.01/3.25          | ~ (m1_pre_topc @ X40 @ X41))),
% 3.01/3.25      inference('simplify', [status(thm)], ['55'])).
% 3.01/3.25  thf('57', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.01/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 3.01/3.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.01/3.25          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 3.01/3.25          | (v1_tsep_1 @ X0 @ sk_D)
% 3.01/3.25          | ~ (l1_pre_topc @ sk_D)
% 3.01/3.25          | ~ (v2_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['54', '56'])).
% 3.01/3.25  thf('58', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf(cc1_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.01/3.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 3.01/3.25  thf('60', plain,
% 3.01/3.25      (![X1 : $i, X2 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X1 @ X2)
% 3.01/3.25          | (v2_pre_topc @ X1)
% 3.01/3.25          | ~ (l1_pre_topc @ X2)
% 3.01/3.25          | ~ (v2_pre_topc @ X2))),
% 3.01/3.25      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 3.01/3.25  thf('61', plain,
% 3.01/3.25      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['59', '60'])).
% 3.01/3.25  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('64', plain, ((v2_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.01/3.25  thf('65', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.01/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 3.01/3.25          | ~ (m1_pre_topc @ X0 @ sk_D)
% 3.01/3.25          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 3.01/3.25          | (v1_tsep_1 @ X0 @ sk_D))),
% 3.01/3.25      inference('demod', [status(thm)], ['57', '58', '64'])).
% 3.01/3.25  thf('66', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_C_1)
% 3.01/3.25        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 3.01/3.25        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 3.01/3.25        | ~ (m1_pre_topc @ sk_C_1 @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['53', '65'])).
% 3.01/3.25  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['18', '19'])).
% 3.01/3.25  thf(d1_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ( v2_pre_topc @ A ) <=>
% 3.01/3.25         ( ( ![B:$i]:
% 3.01/3.25             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25               ( ![C:$i]:
% 3.01/3.25                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 3.01/3.25                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 3.01/3.25                     ( r2_hidden @
% 3.01/3.25                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 3.01/3.25                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 3.01/3.25           ( ![B:$i]:
% 3.01/3.25             ( ( m1_subset_1 @
% 3.01/3.25                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.01/3.25               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 3.01/3.25                 ( r2_hidden @
% 3.01/3.25                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 3.01/3.25                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 3.01/3.25           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_2, axiom,
% 3.01/3.25    (![B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_5 @ B @ A ) <=>
% 3.01/3.25       ( ( m1_subset_1 @
% 3.01/3.25           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.01/3.25         ( zip_tseitin_4 @ B @ A ) ) ))).
% 3.01/3.25  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_4, axiom,
% 3.01/3.25    (![B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_4 @ B @ A ) <=>
% 3.01/3.25       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 3.01/3.25         ( r2_hidden @
% 3.01/3.25           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_6, axiom,
% 3.01/3.25    (![B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_3 @ B @ A ) <=>
% 3.01/3.25       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_8, axiom,
% 3.01/3.25    (![C:$i,B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 3.01/3.25       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 3.01/3.25  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_10, axiom,
% 3.01/3.25    (![C:$i,B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 3.01/3.25       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 3.01/3.25         ( r2_hidden @
% 3.01/3.25           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 3.01/3.25  thf(zf_stmt_12, axiom,
% 3.01/3.25    (![C:$i,B:$i,A:$i]:
% 3.01/3.25     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 3.01/3.25       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 3.01/3.25         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 3.01/3.25  thf(zf_stmt_13, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ( v2_pre_topc @ A ) <=>
% 3.01/3.25         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 3.01/3.25           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 3.01/3.25           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 3.01/3.25  thf('68', plain,
% 3.01/3.25      (![X25 : $i]:
% 3.01/3.25         (~ (v2_pre_topc @ X25)
% 3.01/3.25          | (r2_hidden @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25))
% 3.01/3.25          | ~ (l1_pre_topc @ X25))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.01/3.25  thf('69', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (v1_pre_topc @ X0)
% 3.01/3.25          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 3.01/3.25  thf('70', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (v1_pre_topc @ X0)
% 3.01/3.25          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 3.01/3.25  thf('71', plain,
% 3.01/3.25      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 3.01/3.25      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.01/3.25  thf(t65_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( l1_pre_topc @ B ) =>
% 3.01/3.25           ( ( m1_pre_topc @ A @ B ) <=>
% 3.01/3.25             ( m1_pre_topc @
% 3.01/3.25               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 3.01/3.25  thf('72', plain,
% 3.01/3.25      (![X38 : $i, X39 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X38)
% 3.01/3.25          | ~ (m1_pre_topc @ X39 @ 
% 3.01/3.25               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 3.01/3.25          | (m1_pre_topc @ X39 @ X38)
% 3.01/3.25          | ~ (l1_pre_topc @ X39))),
% 3.01/3.25      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.01/3.25  thf('73', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ 
% 3.01/3.25               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | (m1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('sup-', [status(thm)], ['71', '72'])).
% 3.01/3.25  thf('74', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ 
% 3.01/3.25               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.01/3.25      inference('simplify', [status(thm)], ['73'])).
% 3.01/3.25  thf('75', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('sup-', [status(thm)], ['70', '74'])).
% 3.01/3.25  thf('76', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         ((m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('simplify', [status(thm)], ['75'])).
% 3.01/3.25  thf('77', plain,
% 3.01/3.25      (![X30 : $i, X31 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X30 @ X31)
% 3.01/3.25          | (l1_pre_topc @ X30)
% 3.01/3.25          | ~ (l1_pre_topc @ X31))),
% 3.01/3.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.01/3.25  thf('78', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (l1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.01/3.25      inference('sup-', [status(thm)], ['76', '77'])).
% 3.01/3.25  thf('79', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         ((l1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('simplify', [status(thm)], ['78'])).
% 3.01/3.25  thf('80', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         ((m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (v1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('simplify', [status(thm)], ['75'])).
% 3.01/3.25  thf('81', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('82', plain,
% 3.01/3.25      (![X38 : $i, X39 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X38)
% 3.01/3.25          | ~ (m1_pre_topc @ X39 @ 
% 3.01/3.25               (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 3.01/3.25          | (m1_pre_topc @ X39 @ X38)
% 3.01/3.25          | ~ (l1_pre_topc @ X39))),
% 3.01/3.25      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.01/3.25  thf('83', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ X0 @ sk_C_1)
% 3.01/3.25          | ~ (l1_pre_topc @ sk_C_1))),
% 3.01/3.25      inference('sup-', [status(thm)], ['81', '82'])).
% 3.01/3.25  thf('84', plain, ((l1_pre_topc @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['18', '19'])).
% 3.01/3.25  thf('85', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X0 @ sk_D)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ X0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['83', '84'])).
% 3.01/3.25  thf('86', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D)
% 3.01/3.25        | (m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)
% 3.01/3.25        | ~ (l1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 3.01/3.25      inference('sup-', [status(thm)], ['80', '85'])).
% 3.01/3.25  thf('87', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('88', plain,
% 3.01/3.25      ((~ (v1_pre_topc @ sk_D)
% 3.01/3.25        | (m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)
% 3.01/3.25        | ~ (l1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 3.01/3.25      inference('demod', [status(thm)], ['86', '87'])).
% 3.01/3.25  thf('89', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D)
% 3.01/3.25        | (m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['79', '88'])).
% 3.01/3.25  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('91', plain,
% 3.01/3.25      ((~ (v1_pre_topc @ sk_D)
% 3.01/3.25        | (m1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D))),
% 3.01/3.25      inference('demod', [status(thm)], ['89', '90'])).
% 3.01/3.25  thf('92', plain,
% 3.01/3.25      (((m1_pre_topc @ 
% 3.01/3.25         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D))),
% 3.01/3.25      inference('simplify', [status(thm)], ['91'])).
% 3.01/3.25  thf('93', plain, ((v1_pre_topc @ sk_D)),
% 3.01/3.25      inference('clc', [status(thm)], ['21', '22'])).
% 3.01/3.25  thf('94', plain,
% 3.01/3.25      ((m1_pre_topc @ 
% 3.01/3.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['92', '93'])).
% 3.01/3.25  thf('95', plain,
% 3.01/3.25      (![X30 : $i, X31 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X30 @ X31)
% 3.01/3.25          | (l1_pre_topc @ X30)
% 3.01/3.25          | ~ (l1_pre_topc @ X31))),
% 3.01/3.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.01/3.25  thf('96', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_C_1)
% 3.01/3.25        | (l1_pre_topc @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 3.01/3.25      inference('sup-', [status(thm)], ['94', '95'])).
% 3.01/3.25  thf('97', plain, ((l1_pre_topc @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['18', '19'])).
% 3.01/3.25  thf('98', plain,
% 3.01/3.25      ((l1_pre_topc @ 
% 3.01/3.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 3.01/3.25      inference('demod', [status(thm)], ['96', '97'])).
% 3.01/3.25  thf('99', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ 
% 3.01/3.25               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 3.01/3.25      inference('simplify', [status(thm)], ['73'])).
% 3.01/3.25  thf('100', plain,
% 3.01/3.25      (((m1_pre_topc @ 
% 3.01/3.25         (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_D)
% 3.01/3.25        | ~ (l1_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['98', '99'])).
% 3.01/3.25  thf('101', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('102', plain,
% 3.01/3.25      ((m1_pre_topc @ 
% 3.01/3.25        (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)) @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['100', '101'])).
% 3.01/3.25  thf('103', plain,
% 3.01/3.25      (((m1_pre_topc @ sk_D @ sk_D)
% 3.01/3.25        | ~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | ~ (v1_pre_topc @ sk_D))),
% 3.01/3.25      inference('sup+', [status(thm)], ['69', '102'])).
% 3.01/3.25  thf('104', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('105', plain, ((v1_pre_topc @ sk_D)),
% 3.01/3.25      inference('clc', [status(thm)], ['21', '22'])).
% 3.01/3.25  thf('106', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.01/3.25  thf('107', plain,
% 3.01/3.25      (![X43 : $i, X44 : $i]:
% 3.01/3.25         (~ (m1_pre_topc @ X43 @ X44)
% 3.01/3.25          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 3.01/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 3.01/3.25          | ~ (l1_pre_topc @ X44))),
% 3.01/3.25      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.01/3.25  thf('108', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 3.01/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 3.01/3.25      inference('sup-', [status(thm)], ['106', '107'])).
% 3.01/3.25  thf('109', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('110', plain,
% 3.01/3.25      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 3.01/3.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 3.01/3.25      inference('demod', [status(thm)], ['108', '109'])).
% 3.01/3.25  thf(d5_pre_topc, axiom,
% 3.01/3.25    (![A:$i]:
% 3.01/3.25     ( ( l1_pre_topc @ A ) =>
% 3.01/3.25       ( ![B:$i]:
% 3.01/3.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.01/3.25           ( ( v3_pre_topc @ B @ A ) <=>
% 3.01/3.25             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 3.01/3.25  thf('111', plain,
% 3.01/3.25      (![X28 : $i, X29 : $i]:
% 3.01/3.25         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.01/3.25          | ~ (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 3.01/3.25          | (v3_pre_topc @ X28 @ X29)
% 3.01/3.25          | ~ (l1_pre_topc @ X29))),
% 3.01/3.25      inference('cnf', [status(esa)], [d5_pre_topc])).
% 3.01/3.25  thf('112', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 3.01/3.25        | ~ (r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 3.01/3.25      inference('sup-', [status(thm)], ['110', '111'])).
% 3.01/3.25  thf('113', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('114', plain,
% 3.01/3.25      (((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 3.01/3.25        | ~ (r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 3.01/3.25      inference('demod', [status(thm)], ['112', '113'])).
% 3.01/3.25  thf('115', plain,
% 3.01/3.25      ((~ (l1_pre_topc @ sk_D)
% 3.01/3.25        | ~ (v2_pre_topc @ sk_D)
% 3.01/3.25        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D))),
% 3.01/3.25      inference('sup-', [status(thm)], ['68', '114'])).
% 3.01/3.25  thf('116', plain, ((l1_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['27', '28'])).
% 3.01/3.25  thf('117', plain, ((v2_pre_topc @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.01/3.25  thf('118', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['115', '116', '117'])).
% 3.01/3.25  thf('119', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['12', '23', '24', '29', '30'])).
% 3.01/3.25  thf('120', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['118', '119'])).
% 3.01/3.25  thf('121', plain,
% 3.01/3.25      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 3.01/3.25         = (sk_D))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('122', plain,
% 3.01/3.25      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 3.01/3.25      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.01/3.25  thf('123', plain,
% 3.01/3.25      (![X38 : $i, X39 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X38)
% 3.01/3.25          | ~ (m1_pre_topc @ X39 @ X38)
% 3.01/3.25          | (m1_pre_topc @ X39 @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)))
% 3.01/3.25          | ~ (l1_pre_topc @ X39))),
% 3.01/3.25      inference('cnf', [status(esa)], [t65_pre_topc])).
% 3.01/3.25  thf('124', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         (~ (l1_pre_topc @ X0)
% 3.01/3.25          | ~ (l1_pre_topc @ X0)
% 3.01/3.25          | (m1_pre_topc @ X0 @ 
% 3.01/3.25             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('sup-', [status(thm)], ['122', '123'])).
% 3.01/3.25  thf('125', plain,
% 3.01/3.25      (![X0 : $i]:
% 3.01/3.25         ((m1_pre_topc @ X0 @ 
% 3.01/3.25           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 3.01/3.25          | ~ (l1_pre_topc @ X0))),
% 3.01/3.25      inference('simplify', [status(thm)], ['124'])).
% 3.01/3.25  thf('126', plain,
% 3.01/3.25      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 3.01/3.25      inference('sup+', [status(thm)], ['121', '125'])).
% 3.01/3.25  thf('127', plain, ((l1_pre_topc @ sk_C_1)),
% 3.01/3.25      inference('demod', [status(thm)], ['18', '19'])).
% 3.01/3.25  thf('128', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['126', '127'])).
% 3.01/3.25  thf('129', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['66', '67', '120', '128'])).
% 3.01/3.25  thf('130', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 3.01/3.25      inference('demod', [status(thm)], ['126', '127'])).
% 3.01/3.25  thf('131', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('132', plain, (((sk_F) = (sk_G))),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('133', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['131', '132'])).
% 3.01/3.25  thf('134', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('demod', [status(thm)], ['131', '132'])).
% 3.01/3.25  thf('135', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('138', plain,
% 3.01/3.25      (((v2_struct_0 @ sk_B_2)
% 3.01/3.25        | (v2_struct_0 @ sk_D)
% 3.01/3.25        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 3.01/3.25        | (v2_struct_0 @ sk_C_1)
% 3.01/3.25        | (v2_struct_0 @ sk_A))),
% 3.01/3.25      inference('demod', [status(thm)],
% 3.01/3.25                ['48', '49', '129', '130', '133', '134', '135', '136', '137'])).
% 3.01/3.25  thf('139', plain, (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('140', plain,
% 3.01/3.25      (((v2_struct_0 @ sk_A)
% 3.01/3.25        | (v2_struct_0 @ sk_C_1)
% 3.01/3.25        | (v2_struct_0 @ sk_D)
% 3.01/3.25        | (v2_struct_0 @ sk_B_2))),
% 3.01/3.25      inference('sup-', [status(thm)], ['138', '139'])).
% 3.01/3.25  thf('141', plain, (~ (v2_struct_0 @ sk_D)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('142', plain,
% 3.01/3.25      (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 3.01/3.25      inference('sup-', [status(thm)], ['140', '141'])).
% 3.01/3.25  thf('143', plain, (~ (v2_struct_0 @ sk_B_2)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('144', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 3.01/3.25      inference('clc', [status(thm)], ['142', '143'])).
% 3.01/3.25  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 3.01/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.25  thf('146', plain, ((v2_struct_0 @ sk_C_1)),
% 3.01/3.25      inference('clc', [status(thm)], ['144', '145'])).
% 3.01/3.25  thf('147', plain, ($false), inference('demod', [status(thm)], ['0', '146'])).
% 3.01/3.25  
% 3.01/3.25  % SZS output end Refutation
% 3.01/3.25  
% 3.01/3.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
