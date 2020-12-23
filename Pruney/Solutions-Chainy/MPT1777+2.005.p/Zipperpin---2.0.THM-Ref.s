%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9gWlEfdFHf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:27 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  240 (3001 expanded)
%              Number of leaves         :   42 ( 871 expanded)
%              Depth                    :   26
%              Number of atoms          : 2177 (89832 expanded)
%              Number of equality atoms :   60 (2526 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( X32 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('22',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( m1_pre_topc @ X12 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('32',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','40','41','46','47','48'])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('66',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X3: $i] :
      ( ~ ( v1_pre_topc @ X3 )
      | ( X3
        = ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ( m1_pre_topc @ X12 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('75',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('77',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78'])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['64','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','84'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','84'])).

thf('88',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('90',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('96',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('98',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['93','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('108',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('116',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('118',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('119',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('121',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','123'])).

thf('125',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','84'])).

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

thf('128',plain,(
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

thf('129',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('132',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('133',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('134',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['130','131','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['126','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('143',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('144',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('147',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ( m1_pre_topc @ X22 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['151','152','153'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('155',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('156',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('158',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['154','163'])).

thf('165',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('166',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('167',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['89','90'])).

thf('168',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('170',plain,(
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

thf('171',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['168','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('176',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('177',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('178',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','84'])).

thf('180',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['144','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('183',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('185',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['141','142','143','183','184'])).

thf('186',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104','105','106','109','116','117','118','185','186'])).

thf('188',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['0','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9gWlEfdFHf
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.90  % Solved by: fo/fo7.sh
% 0.68/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.90  % done 839 iterations in 0.440s
% 0.68/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.90  % SZS output start Refutation
% 0.68/0.90  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.68/0.90  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.68/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.90  thf(sk_F_type, type, sk_F: $i).
% 0.68/0.90  thf(sk_E_type, type, sk_E: $i).
% 0.68/0.90  thf(sk_G_type, type, sk_G: $i).
% 0.68/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.90  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.68/0.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.90  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.90  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.68/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.90  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.90  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.68/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.90  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.68/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.90  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.68/0.90  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.90  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.90  thf(t88_tmap_1, conjecture,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.90             ( l1_pre_topc @ B ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.68/0.90               ( ![D:$i]:
% 0.68/0.90                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.68/0.90                   ( ![E:$i]:
% 0.68/0.90                     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.90                         ( v1_funct_2 @
% 0.68/0.90                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.90                         ( m1_subset_1 @
% 0.68/0.90                           E @ 
% 0.68/0.90                           ( k1_zfmisc_1 @
% 0.68/0.90                             ( k2_zfmisc_1 @
% 0.68/0.90                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.90                       ( ( ( g1_pre_topc @
% 0.68/0.90                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.68/0.90                           ( D ) ) =>
% 0.68/0.90                         ( ![F:$i]:
% 0.68/0.90                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.90                             ( ![G:$i]:
% 0.68/0.90                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.68/0.90                                 ( ( ( ( F ) = ( G ) ) & 
% 0.68/0.90                                     ( r1_tmap_1 @
% 0.68/0.90                                       C @ B @ 
% 0.68/0.90                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.68/0.90                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.90    (~( ![A:$i]:
% 0.68/0.90        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.90            ( l1_pre_topc @ A ) ) =>
% 0.68/0.90          ( ![B:$i]:
% 0.68/0.90            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.90                ( l1_pre_topc @ B ) ) =>
% 0.68/0.90              ( ![C:$i]:
% 0.68/0.90                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.68/0.90                  ( ![D:$i]:
% 0.68/0.90                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.68/0.90                      ( ![E:$i]:
% 0.68/0.90                        ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.90                            ( v1_funct_2 @
% 0.68/0.90                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.90                            ( m1_subset_1 @
% 0.68/0.90                              E @ 
% 0.68/0.90                              ( k1_zfmisc_1 @
% 0.68/0.90                                ( k2_zfmisc_1 @
% 0.68/0.90                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.90                          ( ( ( g1_pre_topc @
% 0.68/0.90                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.68/0.90                              ( D ) ) =>
% 0.68/0.90                            ( ![F:$i]:
% 0.68/0.90                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.90                                ( ![G:$i]:
% 0.68/0.90                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.68/0.90                                    ( ( ( ( F ) = ( G ) ) & 
% 0.68/0.90                                        ( r1_tmap_1 @
% 0.68/0.90                                          C @ B @ 
% 0.68/0.90                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.68/0.90                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.68/0.90    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.68/0.90  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('1', plain,
% 0.68/0.90      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.68/0.90        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('2', plain, (((sk_F) = (sk_G))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('3', plain,
% 0.68/0.90      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.68/0.90        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.68/0.90      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.90  thf('4', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_E @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t86_tmap_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.90             ( l1_pre_topc @ B ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.68/0.90               ( ![D:$i]:
% 0.68/0.90                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.68/0.90                   ( ![E:$i]:
% 0.68/0.90                     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.90                         ( v1_funct_2 @
% 0.68/0.90                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.90                         ( m1_subset_1 @
% 0.68/0.90                           E @ 
% 0.68/0.90                           ( k1_zfmisc_1 @
% 0.68/0.90                             ( k2_zfmisc_1 @
% 0.68/0.90                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.90                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.68/0.90                         ( ![F:$i]:
% 0.68/0.90                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.90                             ( ![G:$i]:
% 0.68/0.90                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.68/0.90                                 ( ( ( F ) = ( G ) ) =>
% 0.68/0.90                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.68/0.90                                     ( r1_tmap_1 @
% 0.68/0.90                                       C @ B @ 
% 0.68/0.90                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('5', plain,
% 0.68/0.90      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X28)
% 0.68/0.90          | ~ (v2_pre_topc @ X28)
% 0.68/0.90          | ~ (l1_pre_topc @ X28)
% 0.68/0.90          | (v2_struct_0 @ X29)
% 0.68/0.90          | ~ (m1_pre_topc @ X29 @ X30)
% 0.68/0.90          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.68/0.90          | ~ (m1_pre_topc @ X31 @ X29)
% 0.68/0.90          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.68/0.90          | ((X32) != (X33))
% 0.68/0.90          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.68/0.90               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.68/0.90          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X32)
% 0.68/0.90          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.68/0.90          | ~ (m1_subset_1 @ X34 @ 
% 0.68/0.90               (k1_zfmisc_1 @ 
% 0.68/0.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.68/0.90          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.68/0.90          | ~ (v1_funct_1 @ X34)
% 0.68/0.90          | ~ (m1_pre_topc @ X31 @ X30)
% 0.68/0.90          | (v2_struct_0 @ X31)
% 0.68/0.90          | ~ (l1_pre_topc @ X30)
% 0.68/0.90          | ~ (v2_pre_topc @ X30)
% 0.68/0.90          | (v2_struct_0 @ X30))),
% 0.68/0.90      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.68/0.90  thf('6', plain,
% 0.68/0.90      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X30)
% 0.68/0.90          | ~ (v2_pre_topc @ X30)
% 0.68/0.90          | ~ (l1_pre_topc @ X30)
% 0.68/0.90          | (v2_struct_0 @ X31)
% 0.68/0.90          | ~ (m1_pre_topc @ X31 @ X30)
% 0.68/0.90          | ~ (v1_funct_1 @ X34)
% 0.68/0.90          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.68/0.90          | ~ (m1_subset_1 @ X34 @ 
% 0.68/0.90               (k1_zfmisc_1 @ 
% 0.68/0.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.68/0.90          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.68/0.90          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 0.68/0.90          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.68/0.90               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.68/0.90          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.68/0.90          | ~ (m1_pre_topc @ X31 @ X29)
% 0.68/0.90          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.68/0.90          | ~ (m1_pre_topc @ X29 @ X30)
% 0.68/0.90          | (v2_struct_0 @ X29)
% 0.68/0.90          | ~ (l1_pre_topc @ X28)
% 0.68/0.90          | ~ (v2_pre_topc @ X28)
% 0.68/0.90          | (v2_struct_0 @ X28))),
% 0.68/0.90      inference('simplify', [status(thm)], ['5'])).
% 0.68/0.90  thf('7', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B)
% 0.68/0.90          | ~ (v2_pre_topc @ sk_B)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_B)
% 0.68/0.90          | (v2_struct_0 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.68/0.90          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.68/0.90          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.68/0.90               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.68/0.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.90          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.68/0.90          | ~ (v1_funct_1 @ sk_E)
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.90          | (v2_struct_0 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v2_struct_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['4', '6'])).
% 0.68/0.90  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('10', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('12', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B)
% 0.68/0.90          | (v2_struct_0 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.68/0.90          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.68/0.90          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.68/0.90               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.68/0.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.90          | (v2_struct_0 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v2_struct_0 @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.68/0.90  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t4_tsep_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_pre_topc @ B @ A ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( m1_pre_topc @ C @ A ) =>
% 0.68/0.90               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.68/0.90                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.68/0.90  thf('15', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X22 @ X23)
% 0.68/0.90          | ~ (m1_pre_topc @ X22 @ X24)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.68/0.90          | ~ (m1_pre_topc @ X24 @ X23)
% 0.68/0.90          | ~ (l1_pre_topc @ X23)
% 0.68/0.90          | ~ (v2_pre_topc @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.68/0.90  thf('16', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ sk_A)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.90  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('19', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.68/0.90  thf('20', plain,
% 0.68/0.90      ((~ (m1_pre_topc @ sk_D @ sk_C)
% 0.68/0.90        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['13', '19'])).
% 0.68/0.90  thf(t2_tsep_1, axiom,
% 0.68/0.90    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.68/0.90  thf('21', plain,
% 0.68/0.90      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.68/0.90      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.68/0.90  thf('22', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(abstractness_v1_pre_topc, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_pre_topc @ A ) =>
% 0.68/0.90       ( ( v1_pre_topc @ A ) =>
% 0.68/0.90         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.68/0.90  thf('23', plain,
% 0.68/0.90      (![X3 : $i]:
% 0.68/0.90         (~ (v1_pre_topc @ X3)
% 0.68/0.90          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.68/0.90          | ~ (l1_pre_topc @ X3))),
% 0.68/0.90      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.68/0.90  thf(t31_pre_topc, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_pre_topc @ A ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( l1_pre_topc @ B ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( l1_pre_topc @ C ) =>
% 0.68/0.90               ( ![D:$i]:
% 0.68/0.90                 ( ( l1_pre_topc @ D ) =>
% 0.68/0.90                   ( ( ( ( g1_pre_topc @
% 0.68/0.90                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.68/0.90                         ( g1_pre_topc @
% 0.68/0.90                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.68/0.90                       ( ( g1_pre_topc @
% 0.68/0.90                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.68/0.90                         ( g1_pre_topc @
% 0.68/0.90                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.68/0.90                       ( m1_pre_topc @ C @ A ) ) =>
% 0.68/0.90                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('24', plain,
% 0.68/0.90      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X11)
% 0.68/0.90          | ~ (l1_pre_topc @ X12)
% 0.68/0.90          | (m1_pre_topc @ X12 @ X11)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.68/0.90          | ~ (m1_pre_topc @ X13 @ X14)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.68/0.90          | ~ (l1_pre_topc @ X13)
% 0.68/0.90          | ~ (l1_pre_topc @ X14))),
% 0.68/0.90      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.68/0.90  thf('25', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.90          | (m1_pre_topc @ X1 @ X2)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X2))),
% 0.68/0.90      inference('eq_res', [status(thm)], ['24'])).
% 0.68/0.90  thf('26', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X2)
% 0.68/0.90          | (m1_pre_topc @ X1 @ X2)
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['25'])).
% 0.68/0.90  thf('27', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X2)
% 0.68/0.90          | ~ (m1_pre_topc @ X2 @ X0)
% 0.68/0.90          | (m1_pre_topc @ X2 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['23', '26'])).
% 0.68/0.90  thf('28', plain,
% 0.68/0.90      (![X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X1)
% 0.68/0.90          | (m1_pre_topc @ X2 @ X1)
% 0.68/0.90          | ~ (m1_pre_topc @ X2 @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.68/0.90          | ~ (l1_pre_topc @ X2)
% 0.68/0.90          | ~ (v1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.68/0.90          | ~ (l1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.90  thf('29', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v1_pre_topc @ sk_D)
% 0.68/0.90          | ~ (l1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.68/0.90          | (m1_pre_topc @ X0 @ sk_C)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['22', '28'])).
% 0.68/0.90  thf('30', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(fc7_pre_topc, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ( ~( v2_struct_0 @
% 0.68/0.90              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.68/0.90         ( v1_pre_topc @
% 0.68/0.90           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.68/0.90  thf('31', plain,
% 0.68/0.90      (![X10 : $i]:
% 0.68/0.90         ((v1_pre_topc @ 
% 0.68/0.90           (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.68/0.90          | ~ (l1_pre_topc @ X10)
% 0.68/0.90          | (v2_struct_0 @ X10))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.68/0.90  thf('32', plain,
% 0.68/0.90      (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.68/0.90      inference('sup+', [status(thm)], ['30', '31'])).
% 0.68/0.90  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(dt_m1_pre_topc, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_pre_topc @ A ) =>
% 0.68/0.90       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.68/0.90  thf('34', plain,
% 0.68/0.90      (![X8 : $i, X9 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.68/0.90  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.90  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('38', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['32', '37'])).
% 0.68/0.90  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('40', plain, ((v1_pre_topc @ sk_D)),
% 0.68/0.90      inference('clc', [status(thm)], ['38', '39'])).
% 0.68/0.90  thf('41', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('43', plain,
% 0.68/0.90      (![X8 : $i, X9 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.68/0.90  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['42', '43'])).
% 0.68/0.90  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('47', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('48', plain, ((l1_pre_topc @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('49', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.68/0.90          | (m1_pre_topc @ X0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['29', '40', '41', '46', '47', '48'])).
% 0.68/0.90  thf('50', plain,
% 0.68/0.90      ((~ (l1_pre_topc @ sk_D)
% 0.68/0.90        | (m1_pre_topc @ sk_D @ sk_C)
% 0.68/0.90        | ~ (l1_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['21', '49'])).
% 0.68/0.90  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('53', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.68/0.90  thf('54', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['20', '53'])).
% 0.68/0.90  thf(d10_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.90  thf('55', plain,
% 0.68/0.90      (![X0 : $i, X2 : $i]:
% 0.68/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.90  thf('56', plain,
% 0.68/0.90      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.68/0.90        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['54', '55'])).
% 0.68/0.90  thf('57', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('59', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X22 @ X23)
% 0.68/0.90          | ~ (m1_pre_topc @ X22 @ X24)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.68/0.90          | ~ (m1_pre_topc @ X24 @ X23)
% 0.68/0.90          | ~ (l1_pre_topc @ X23)
% 0.68/0.90          | ~ (v2_pre_topc @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.68/0.90  thf('60', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ sk_A)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.68/0.90          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.90  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('63', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.68/0.90          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.68/0.90          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.68/0.90  thf('64', plain,
% 0.68/0.90      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.68/0.90        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['57', '63'])).
% 0.68/0.90  thf('65', plain,
% 0.68/0.90      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.68/0.90      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.68/0.90  thf('66', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('67', plain,
% 0.68/0.90      (![X3 : $i]:
% 0.68/0.90         (~ (v1_pre_topc @ X3)
% 0.68/0.90          | ((X3) = (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.68/0.90          | ~ (l1_pre_topc @ X3))),
% 0.68/0.90      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.68/0.90  thf('68', plain,
% 0.68/0.90      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X11)
% 0.68/0.90          | ~ (l1_pre_topc @ X12)
% 0.68/0.90          | (m1_pre_topc @ X12 @ X11)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.68/0.90          | ~ (m1_pre_topc @ X13 @ X14)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.68/0.90          | ~ (l1_pre_topc @ X13)
% 0.68/0.90          | ~ (l1_pre_topc @ X14))),
% 0.68/0.90      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.68/0.90  thf('69', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.90         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X2)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X2)
% 0.68/0.90          | (m1_pre_topc @ X1 @ X3)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X3))),
% 0.68/0.90      inference('sup-', [status(thm)], ['67', '68'])).
% 0.68/0.90  thf('70', plain,
% 0.68/0.90      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X3)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | (m1_pre_topc @ X1 @ X3)
% 0.68/0.90          | ~ (m1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X2)
% 0.68/0.90          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.68/0.90              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.68/0.90          | ~ (l1_pre_topc @ X2)
% 0.68/0.90          | ~ (v1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.68/0.90          | ~ (l1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['69'])).
% 0.68/0.90  thf('71', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ 
% 0.68/0.90             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.68/0.90          | ~ (v1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (m1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.68/0.90          | (m1_pre_topc @ X0 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X1))),
% 0.68/0.90      inference('eq_res', [status(thm)], ['70'])).
% 0.68/0.90  thf('72', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | (m1_pre_topc @ X0 @ X1)
% 0.68/0.90          | ~ (m1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (v1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.68/0.90          | ~ (l1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['71'])).
% 0.68/0.90  thf('73', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v1_pre_topc @ sk_D)
% 0.68/0.90          | ~ (l1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ 
% 0.68/0.90               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.68/0.90          | (m1_pre_topc @ sk_C @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['66', '72'])).
% 0.68/0.90  thf('74', plain, ((v1_pre_topc @ sk_D)),
% 0.68/0.90      inference('clc', [status(thm)], ['38', '39'])).
% 0.68/0.90  thf('75', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('77', plain,
% 0.68/0.90      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('78', plain, ((l1_pre_topc @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('79', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.68/0.90          | (m1_pre_topc @ sk_C @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['73', '74', '75', '76', '77', '78'])).
% 0.68/0.90  thf('80', plain,
% 0.68/0.90      ((~ (l1_pre_topc @ sk_D)
% 0.68/0.90        | (m1_pre_topc @ sk_C @ sk_D)
% 0.68/0.90        | ~ (l1_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['65', '79'])).
% 0.68/0.90  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.68/0.90  thf('84', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['64', '83'])).
% 0.68/0.90  thf('85', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['56', '84'])).
% 0.68/0.90  thf(d3_struct_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.68/0.90  thf('86', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('87', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['56', '84'])).
% 0.68/0.90  thf('88', plain,
% 0.68/0.90      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.68/0.90      inference('sup+', [status(thm)], ['86', '87'])).
% 0.68/0.90  thf('89', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf(dt_l1_pre_topc, axiom,
% 0.68/0.90    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.68/0.90  thf('90', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.90  thf('91', plain, ((l1_struct_0 @ sk_D)),
% 0.68/0.90      inference('sup-', [status(thm)], ['89', '90'])).
% 0.68/0.90  thf('92', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['88', '91'])).
% 0.68/0.90  thf('93', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['85', '92'])).
% 0.68/0.90  thf('94', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('95', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['88', '91'])).
% 0.68/0.90  thf('96', plain,
% 0.68/0.90      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.68/0.90      inference('sup+', [status(thm)], ['94', '95'])).
% 0.68/0.90  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('98', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.90  thf('99', plain, ((l1_struct_0 @ sk_C)),
% 0.68/0.90      inference('sup-', [status(thm)], ['97', '98'])).
% 0.68/0.90  thf('100', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['96', '99'])).
% 0.68/0.90  thf('101', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['93', '100'])).
% 0.68/0.90  thf('102', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B)
% 0.68/0.90          | (v2_struct_0 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.68/0.90          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.68/0.90          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.68/0.90               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.68/0.90          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.68/0.90          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.90          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.90          | (v2_struct_0 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v2_struct_0 @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['12', '101'])).
% 0.68/0.90  thf('103', plain,
% 0.68/0.90      (((v2_struct_0 @ sk_A)
% 0.68/0.90        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.90        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.90        | (v2_struct_0 @ sk_C)
% 0.68/0.90        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.68/0.90        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.68/0.90        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.68/0.90        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.68/0.90        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.68/0.90        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.68/0.90        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.68/0.90        | (v2_struct_0 @ sk_D)
% 0.68/0.90        | (v2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['3', '102'])).
% 0.68/0.90  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('106', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('107', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['88', '91'])).
% 0.68/0.90  thf('108', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['96', '99'])).
% 0.68/0.90  thf('109', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['107', '108'])).
% 0.68/0.90  thf('110', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('111', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('112', plain, (((sk_F) = (sk_G))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('113', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['111', '112'])).
% 0.68/0.90  thf('114', plain,
% 0.68/0.90      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.68/0.90      inference('sup+', [status(thm)], ['110', '113'])).
% 0.68/0.90  thf('115', plain, ((l1_struct_0 @ sk_C)),
% 0.68/0.90      inference('sup-', [status(thm)], ['97', '98'])).
% 0.68/0.90  thf('116', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['114', '115'])).
% 0.68/0.90  thf('117', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['114', '115'])).
% 0.68/0.90  thf('118', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.68/0.90  thf('119', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('120', plain,
% 0.68/0.90      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.68/0.90      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.68/0.90  thf(t1_tsep_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( l1_pre_topc @ A ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_pre_topc @ B @ A ) =>
% 0.68/0.90           ( m1_subset_1 @
% 0.68/0.90             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.68/0.90  thf('121', plain,
% 0.68/0.90      (![X19 : $i, X20 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X19 @ X20)
% 0.68/0.90          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.90          | ~ (l1_pre_topc @ X20))),
% 0.68/0.90      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.68/0.90  thf('122', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['120', '121'])).
% 0.68/0.90  thf('123', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['122'])).
% 0.68/0.90  thf('124', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.68/0.90          | ~ (l1_struct_0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['119', '123'])).
% 0.68/0.90  thf('125', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.90  thf('126', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.68/0.90      inference('clc', [status(thm)], ['124', '125'])).
% 0.68/0.90  thf('127', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['56', '84'])).
% 0.68/0.90  thf(t16_tsep_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_pre_topc @ B @ A ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.90               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.68/0.90                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.68/0.90                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('128', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X16 @ X17)
% 0.68/0.90          | ((X18) != (u1_struct_0 @ X16))
% 0.68/0.90          | ~ (v3_pre_topc @ X18 @ X17)
% 0.68/0.90          | (v1_tsep_1 @ X16 @ X17)
% 0.68/0.90          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.90          | ~ (l1_pre_topc @ X17)
% 0.68/0.90          | ~ (v2_pre_topc @ X17))),
% 0.68/0.90      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.68/0.90  thf('129', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X17)
% 0.68/0.90          | ~ (l1_pre_topc @ X17)
% 0.68/0.90          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.68/0.90               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.90          | (v1_tsep_1 @ X16 @ X17)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.68/0.90          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.68/0.90      inference('simplify', [status(thm)], ['128'])).
% 0.68/0.90  thf('130', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ sk_D)
% 0.68/0.90          | ~ (l1_pre_topc @ sk_D)
% 0.68/0.90          | ~ (v2_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['127', '129'])).
% 0.68/0.90  thf('131', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('132', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(cc1_pre_topc, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.68/0.90  thf('133', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X4 @ X5)
% 0.68/0.90          | (v2_pre_topc @ X4)
% 0.68/0.90          | ~ (l1_pre_topc @ X5)
% 0.68/0.90          | ~ (v2_pre_topc @ X5))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.68/0.90  thf('134', plain,
% 0.68/0.90      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['132', '133'])).
% 0.68/0.90  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('137', plain, ((v2_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.68/0.90  thf('138', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['130', '131', '137'])).
% 0.68/0.90  thf('139', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['107', '108'])).
% 0.68/0.90  thf('140', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['138', '139'])).
% 0.68/0.90  thf('141', plain,
% 0.68/0.90      ((~ (l1_pre_topc @ sk_C)
% 0.68/0.90        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.68/0.90        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.68/0.90        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['126', '140'])).
% 0.68/0.90  thf('142', plain, ((l1_pre_topc @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('143', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['107', '108'])).
% 0.68/0.90  thf('144', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('145', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('146', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.68/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.90  thf('147', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.68/0.90      inference('simplify', [status(thm)], ['146'])).
% 0.68/0.90  thf('148', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X22 @ X23)
% 0.68/0.90          | ~ (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.68/0.90          | (m1_pre_topc @ X22 @ X24)
% 0.68/0.90          | ~ (m1_pre_topc @ X24 @ X23)
% 0.68/0.90          | ~ (l1_pre_topc @ X23)
% 0.68/0.90          | ~ (v2_pre_topc @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.68/0.90  thf('149', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X1)
% 0.68/0.90          | (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['147', '148'])).
% 0.68/0.90  thf('150', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X1)
% 0.68/0.90          | ~ (l1_pre_topc @ X1)
% 0.68/0.90          | ~ (v2_pre_topc @ X1))),
% 0.68/0.90      inference('simplify', [status(thm)], ['149'])).
% 0.68/0.90  thf('151', plain,
% 0.68/0.90      ((~ (v2_pre_topc @ sk_A)
% 0.68/0.90        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.90        | (m1_pre_topc @ sk_D @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['145', '150'])).
% 0.68/0.90  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('154', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.68/0.90  thf(fc10_tops_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.90       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.68/0.90  thf('155', plain,
% 0.68/0.90      (![X15 : $i]:
% 0.68/0.90         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.68/0.90          | ~ (l1_pre_topc @ X15)
% 0.68/0.90          | ~ (v2_pre_topc @ X15))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.68/0.90  thf('156', plain,
% 0.68/0.90      (![X6 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('157', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['122'])).
% 0.68/0.90  thf('158', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X17)
% 0.68/0.90          | ~ (l1_pre_topc @ X17)
% 0.68/0.90          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.68/0.90               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.90          | (v1_tsep_1 @ X16 @ X17)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.68/0.90          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.68/0.90      inference('simplify', [status(thm)], ['128'])).
% 0.68/0.90  thf('159', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['157', '158'])).
% 0.68/0.90  thf('160', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['159'])).
% 0.68/0.90  thf('161', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.68/0.90          | ~ (l1_struct_0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['156', '160'])).
% 0.68/0.90  thf('162', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (l1_struct_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['155', '161'])).
% 0.68/0.90  thf('163', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_struct_0 @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['162'])).
% 0.68/0.90  thf('164', plain,
% 0.68/0.90      ((~ (v2_pre_topc @ sk_D)
% 0.68/0.90        | ~ (l1_pre_topc @ sk_D)
% 0.68/0.90        | (v1_tsep_1 @ sk_D @ sk_D)
% 0.68/0.90        | ~ (l1_struct_0 @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['154', '163'])).
% 0.68/0.90  thf('165', plain, ((v2_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.68/0.90  thf('166', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('167', plain, ((l1_struct_0 @ sk_D)),
% 0.68/0.90      inference('sup-', [status(thm)], ['89', '90'])).
% 0.68/0.90  thf('168', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.68/0.90  thf('169', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['122'])).
% 0.68/0.90  thf('170', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.90         (~ (m1_pre_topc @ X16 @ X17)
% 0.68/0.90          | ((X18) != (u1_struct_0 @ X16))
% 0.68/0.90          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.68/0.90          | ~ (m1_pre_topc @ X16 @ X17)
% 0.68/0.90          | (v3_pre_topc @ X18 @ X17)
% 0.68/0.90          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.90          | ~ (l1_pre_topc @ X17)
% 0.68/0.90          | ~ (v2_pre_topc @ X17))),
% 0.68/0.90      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.68/0.90  thf('171', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X17)
% 0.68/0.90          | ~ (l1_pre_topc @ X17)
% 0.68/0.90          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.68/0.90               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.90          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.68/0.90          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.68/0.90          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.68/0.90      inference('simplify', [status(thm)], ['170'])).
% 0.68/0.90  thf('172', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0)
% 0.68/0.90          | ~ (v2_pre_topc @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['169', '171'])).
% 0.68/0.90  thf('173', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v2_pre_topc @ X0)
% 0.68/0.90          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.68/0.90          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.68/0.90          | ~ (m1_pre_topc @ X0 @ X0)
% 0.68/0.90          | ~ (l1_pre_topc @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['172'])).
% 0.68/0.90  thf('174', plain,
% 0.68/0.90      ((~ (l1_pre_topc @ sk_D)
% 0.68/0.90        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.68/0.90        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.68/0.90        | ~ (v2_pre_topc @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['168', '173'])).
% 0.68/0.90  thf('175', plain, ((l1_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.90  thf('176', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.68/0.90  thf('177', plain, ((v2_pre_topc @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.68/0.90  thf('178', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 0.68/0.90  thf('179', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['56', '84'])).
% 0.68/0.90  thf('180', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['178', '179'])).
% 0.68/0.90  thf('181', plain,
% 0.68/0.90      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D) | ~ (l1_struct_0 @ sk_C))),
% 0.68/0.90      inference('sup+', [status(thm)], ['144', '180'])).
% 0.68/0.90  thf('182', plain, ((l1_struct_0 @ sk_C)),
% 0.68/0.90      inference('sup-', [status(thm)], ['97', '98'])).
% 0.68/0.90  thf('183', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['181', '182'])).
% 0.68/0.90  thf('184', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.68/0.90  thf('185', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.68/0.90      inference('demod', [status(thm)], ['141', '142', '143', '183', '184'])).
% 0.68/0.90  thf('186', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('187', plain,
% 0.68/0.90      (((v2_struct_0 @ sk_A)
% 0.68/0.90        | (v2_struct_0 @ sk_C)
% 0.68/0.90        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.68/0.90        | (v2_struct_0 @ sk_D)
% 0.68/0.90        | (v2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)],
% 0.68/0.90                ['103', '104', '105', '106', '109', '116', '117', '118', 
% 0.68/0.90                 '185', '186'])).
% 0.68/0.90  thf('188', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('189', plain,
% 0.68/0.90      (((v2_struct_0 @ sk_B)
% 0.68/0.90        | (v2_struct_0 @ sk_D)
% 0.68/0.90        | (v2_struct_0 @ sk_C)
% 0.68/0.90        | (v2_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['187', '188'])).
% 0.68/0.90  thf('190', plain, (~ (v2_struct_0 @ sk_D)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('191', plain,
% 0.68/0.90      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['189', '190'])).
% 0.68/0.90  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('193', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.68/0.90      inference('clc', [status(thm)], ['191', '192'])).
% 0.68/0.90  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('195', plain, ((v2_struct_0 @ sk_C)),
% 0.68/0.90      inference('clc', [status(thm)], ['193', '194'])).
% 0.68/0.90  thf('196', plain, ($false), inference('demod', [status(thm)], ['0', '195'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
