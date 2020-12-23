%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clCgq8mGDG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:29 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 740 expanded)
%              Number of leaves         :   42 ( 230 expanded)
%              Depth                    :   26
%              Number of atoms          : 2057 (21923 expanded)
%              Number of equality atoms :   35 ( 563 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( m1_pre_topc @ X9 @ X8 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
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
    ! [X7: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['29','40','41','46','47','48'])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('52',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','53','54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('57',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( m1_pre_topc @ X9 @ X8 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('66',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('68',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('77',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('84',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

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

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ( v1_tsep_1 @ X18 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('89',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('90',plain,(
    ! [X12: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

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

thf('96',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('97',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('106',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v3_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('115',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('116',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('118',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('121',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['114','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('127',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('129',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('134',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126','132','133'])).

thf('135',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('138',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('140',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126','132','133'])).

thf('142',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('143',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('144',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['113','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('147',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('148',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('149',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['145','146','147','150'])).

thf('152',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126','132','133'])).

thf('153',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('154',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('155',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['87','151','152','153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','159'])).

thf('161',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['0','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clCgq8mGDG
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.61/1.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.82  % Solved by: fo/fo7.sh
% 1.61/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.82  % done 2496 iterations in 1.367s
% 1.61/1.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.82  % SZS output start Refutation
% 1.61/1.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.61/1.82  thf(sk_C_type, type, sk_C: $i).
% 1.61/1.82  thf(sk_F_type, type, sk_F: $i).
% 1.61/1.82  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.61/1.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.61/1.82  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.61/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.82  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.61/1.82  thf(sk_D_type, type, sk_D: $i).
% 1.61/1.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.61/1.82  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.61/1.82  thf(sk_E_type, type, sk_E: $i).
% 1.61/1.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.61/1.82  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.61/1.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.61/1.82  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.61/1.82  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.61/1.82  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.61/1.82  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.61/1.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.61/1.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.61/1.82  thf(sk_G_type, type, sk_G: $i).
% 1.61/1.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.61/1.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.61/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.61/1.82  thf(t88_tmap_1, conjecture,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.61/1.82             ( l1_pre_topc @ B ) ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.61/1.82               ( ![D:$i]:
% 1.61/1.82                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.61/1.82                   ( ![E:$i]:
% 1.61/1.82                     ( ( ( v1_funct_1 @ E ) & 
% 1.61/1.82                         ( v1_funct_2 @
% 1.61/1.82                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.61/1.82                         ( m1_subset_1 @
% 1.61/1.82                           E @ 
% 1.61/1.82                           ( k1_zfmisc_1 @
% 1.61/1.82                             ( k2_zfmisc_1 @
% 1.61/1.82                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.61/1.82                       ( ( ( g1_pre_topc @
% 1.61/1.82                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.61/1.82                           ( D ) ) =>
% 1.61/1.82                         ( ![F:$i]:
% 1.61/1.82                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.61/1.82                             ( ![G:$i]:
% 1.61/1.82                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.61/1.82                                 ( ( ( ( F ) = ( G ) ) & 
% 1.61/1.82                                     ( r1_tmap_1 @
% 1.61/1.82                                       C @ B @ 
% 1.61/1.82                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.61/1.82                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.61/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.82    (~( ![A:$i]:
% 1.61/1.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.61/1.82            ( l1_pre_topc @ A ) ) =>
% 1.61/1.82          ( ![B:$i]:
% 1.61/1.82            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.61/1.82                ( l1_pre_topc @ B ) ) =>
% 1.61/1.82              ( ![C:$i]:
% 1.61/1.82                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.61/1.82                  ( ![D:$i]:
% 1.61/1.82                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.61/1.82                      ( ![E:$i]:
% 1.61/1.82                        ( ( ( v1_funct_1 @ E ) & 
% 1.61/1.82                            ( v1_funct_2 @
% 1.61/1.82                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.61/1.82                            ( m1_subset_1 @
% 1.61/1.82                              E @ 
% 1.61/1.82                              ( k1_zfmisc_1 @
% 1.61/1.82                                ( k2_zfmisc_1 @
% 1.61/1.82                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.61/1.82                          ( ( ( g1_pre_topc @
% 1.61/1.82                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.61/1.82                              ( D ) ) =>
% 1.61/1.82                            ( ![F:$i]:
% 1.61/1.82                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.61/1.82                                ( ![G:$i]:
% 1.61/1.82                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.61/1.82                                    ( ( ( ( F ) = ( G ) ) & 
% 1.61/1.82                                        ( r1_tmap_1 @
% 1.61/1.82                                          C @ B @ 
% 1.61/1.82                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.61/1.82                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.61/1.82    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.61/1.82  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('1', plain,
% 1.61/1.82      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.61/1.82        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('2', plain, (((sk_F) = (sk_G))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('3', plain,
% 1.61/1.82      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.61/1.82        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.61/1.82      inference('demod', [status(thm)], ['1', '2'])).
% 1.61/1.82  thf('4', plain,
% 1.61/1.82      ((m1_subset_1 @ sk_E @ 
% 1.61/1.82        (k1_zfmisc_1 @ 
% 1.61/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(t86_tmap_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.61/1.82             ( l1_pre_topc @ B ) ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.61/1.82               ( ![D:$i]:
% 1.61/1.82                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.61/1.82                   ( ![E:$i]:
% 1.61/1.82                     ( ( ( v1_funct_1 @ E ) & 
% 1.61/1.82                         ( v1_funct_2 @
% 1.61/1.82                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.61/1.82                         ( m1_subset_1 @
% 1.61/1.82                           E @ 
% 1.61/1.82                           ( k1_zfmisc_1 @
% 1.61/1.82                             ( k2_zfmisc_1 @
% 1.61/1.82                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.61/1.82                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.61/1.82                         ( ![F:$i]:
% 1.61/1.82                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.61/1.82                             ( ![G:$i]:
% 1.61/1.82                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.61/1.82                                 ( ( ( F ) = ( G ) ) =>
% 1.61/1.82                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.61/1.82                                     ( r1_tmap_1 @
% 1.61/1.82                                       C @ B @ 
% 1.61/1.82                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.61/1.82  thf('5', plain,
% 1.61/1.82      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.61/1.82         ((v2_struct_0 @ X30)
% 1.61/1.82          | ~ (v2_pre_topc @ X30)
% 1.61/1.82          | ~ (l1_pre_topc @ X30)
% 1.61/1.82          | (v2_struct_0 @ X31)
% 1.61/1.82          | ~ (m1_pre_topc @ X31 @ X32)
% 1.61/1.82          | ~ (v1_tsep_1 @ X33 @ X31)
% 1.61/1.82          | ~ (m1_pre_topc @ X33 @ X31)
% 1.61/1.82          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X31))
% 1.61/1.82          | ((X34) != (X35))
% 1.61/1.82          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 1.61/1.82               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 1.61/1.82          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X34)
% 1.61/1.82          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 1.61/1.82          | ~ (m1_subset_1 @ X36 @ 
% 1.61/1.82               (k1_zfmisc_1 @ 
% 1.61/1.82                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 1.61/1.82          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 1.61/1.82          | ~ (v1_funct_1 @ X36)
% 1.61/1.82          | ~ (m1_pre_topc @ X33 @ X32)
% 1.61/1.82          | (v2_struct_0 @ X33)
% 1.61/1.82          | ~ (l1_pre_topc @ X32)
% 1.61/1.82          | ~ (v2_pre_topc @ X32)
% 1.61/1.82          | (v2_struct_0 @ X32))),
% 1.61/1.82      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.61/1.82  thf('6', plain,
% 1.61/1.82      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X35 : $i, X36 : $i]:
% 1.61/1.82         ((v2_struct_0 @ X32)
% 1.61/1.82          | ~ (v2_pre_topc @ X32)
% 1.61/1.82          | ~ (l1_pre_topc @ X32)
% 1.61/1.82          | (v2_struct_0 @ X33)
% 1.61/1.82          | ~ (m1_pre_topc @ X33 @ X32)
% 1.61/1.82          | ~ (v1_funct_1 @ X36)
% 1.61/1.82          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 1.61/1.82          | ~ (m1_subset_1 @ X36 @ 
% 1.61/1.82               (k1_zfmisc_1 @ 
% 1.61/1.82                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 1.61/1.82          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 1.61/1.82          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X35)
% 1.61/1.82          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 1.61/1.82               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 1.61/1.82          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X31))
% 1.61/1.82          | ~ (m1_pre_topc @ X33 @ X31)
% 1.61/1.82          | ~ (v1_tsep_1 @ X33 @ X31)
% 1.61/1.82          | ~ (m1_pre_topc @ X31 @ X32)
% 1.61/1.82          | (v2_struct_0 @ X31)
% 1.61/1.82          | ~ (l1_pre_topc @ X30)
% 1.61/1.82          | ~ (v2_pre_topc @ X30)
% 1.61/1.82          | (v2_struct_0 @ X30))),
% 1.61/1.82      inference('simplify', [status(thm)], ['5'])).
% 1.61/1.82  thf('7', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.82         ((v2_struct_0 @ sk_B)
% 1.61/1.82          | ~ (v2_pre_topc @ sk_B)
% 1.61/1.82          | ~ (l1_pre_topc @ sk_B)
% 1.61/1.82          | (v2_struct_0 @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.61/1.82          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.61/1.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.61/1.82          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.61/1.82               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.61/1.82          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.61/1.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.61/1.82          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.61/1.82          | ~ (v1_funct_1 @ sk_E)
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ X0)
% 1.61/1.82          | (v2_struct_0 @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | (v2_struct_0 @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['4', '6'])).
% 1.61/1.82  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('10', plain,
% 1.61/1.82      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('12', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.82         ((v2_struct_0 @ sk_B)
% 1.61/1.82          | (v2_struct_0 @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.61/1.82          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.61/1.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.61/1.82          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.61/1.82               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.61/1.82          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.61/1.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ X0)
% 1.61/1.82          | (v2_struct_0 @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | (v2_struct_0 @ X0))),
% 1.61/1.82      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.61/1.82  thf('13', plain,
% 1.61/1.82      (((v2_struct_0 @ sk_A)
% 1.61/1.82        | ~ (v2_pre_topc @ sk_A)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_A)
% 1.61/1.82        | (v2_struct_0 @ sk_C)
% 1.61/1.82        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.61/1.82        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.61/1.82        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.61/1.82        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.61/1.82        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.61/1.82        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.61/1.82        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.61/1.82        | (v2_struct_0 @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_B))),
% 1.61/1.82      inference('sup-', [status(thm)], ['3', '12'])).
% 1.61/1.82  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('18', plain, (((sk_F) = (sk_G))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['17', '18'])).
% 1.61/1.82  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(t2_tsep_1, axiom,
% 1.61/1.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.61/1.82  thf('21', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf('22', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(abstractness_v1_pre_topc, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( l1_pre_topc @ A ) =>
% 1.61/1.82       ( ( v1_pre_topc @ A ) =>
% 1.61/1.82         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.61/1.82  thf('23', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v1_pre_topc @ X0)
% 1.61/1.82          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.61/1.82  thf(t31_pre_topc, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( l1_pre_topc @ A ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( l1_pre_topc @ B ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( l1_pre_topc @ C ) =>
% 1.61/1.82               ( ![D:$i]:
% 1.61/1.82                 ( ( l1_pre_topc @ D ) =>
% 1.61/1.82                   ( ( ( ( g1_pre_topc @
% 1.61/1.82                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.61/1.82                         ( g1_pre_topc @
% 1.61/1.82                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.61/1.82                       ( ( g1_pre_topc @
% 1.61/1.82                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.61/1.82                         ( g1_pre_topc @
% 1.61/1.82                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 1.61/1.82                       ( m1_pre_topc @ C @ A ) ) =>
% 1.61/1.82                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.61/1.82  thf('24', plain,
% 1.61/1.82      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X8)
% 1.61/1.82          | ~ (l1_pre_topc @ X9)
% 1.61/1.82          | (m1_pre_topc @ X9 @ X8)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 1.61/1.82          | ~ (m1_pre_topc @ X10 @ X11)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 1.61/1.82          | ~ (l1_pre_topc @ X10)
% 1.61/1.82          | ~ (l1_pre_topc @ X11))),
% 1.61/1.82      inference('cnf', [status(esa)], [t31_pre_topc])).
% 1.61/1.82  thf('25', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.82         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X2)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X2)
% 1.61/1.82          | (m1_pre_topc @ X1 @ X3)
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X3))),
% 1.61/1.82      inference('sup-', [status(thm)], ['23', '24'])).
% 1.61/1.82  thf('26', plain,
% 1.61/1.82      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X3)
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | (m1_pre_topc @ X1 @ X3)
% 1.61/1.82          | ~ (m1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X2)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 1.61/1.82          | ~ (l1_pre_topc @ X2)
% 1.61/1.82          | ~ (v1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.61/1.82          | ~ (l1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 1.61/1.82      inference('simplify', [status(thm)], ['25'])).
% 1.61/1.82  thf('27', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ 
% 1.61/1.82             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.61/1.82          | ~ (v1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ~ (m1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 1.61/1.82          | (m1_pre_topc @ X0 @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X1))),
% 1.61/1.82      inference('eq_res', [status(thm)], ['26'])).
% 1.61/1.82  thf('28', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | (m1_pre_topc @ X0 @ X1)
% 1.61/1.82          | ~ (m1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ~ (v1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.61/1.82      inference('simplify', [status(thm)], ['27'])).
% 1.61/1.82  thf('29', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v1_pre_topc @ sk_D)
% 1.61/1.82          | ~ (l1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 1.61/1.82          | (m1_pre_topc @ sk_C @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['22', '28'])).
% 1.61/1.82  thf('30', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(fc7_pre_topc, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ( ~( v2_struct_0 @
% 1.61/1.82              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 1.61/1.82         ( v1_pre_topc @
% 1.61/1.82           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.61/1.82  thf('31', plain,
% 1.61/1.82      (![X7 : $i]:
% 1.61/1.82         ((v1_pre_topc @ 
% 1.61/1.82           (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 1.61/1.82          | ~ (l1_pre_topc @ X7)
% 1.61/1.82          | (v2_struct_0 @ X7))),
% 1.61/1.82      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 1.61/1.82  thf('32', plain,
% 1.61/1.82      (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup+', [status(thm)], ['30', '31'])).
% 1.61/1.82  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(dt_m1_pre_topc, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( l1_pre_topc @ A ) =>
% 1.61/1.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.61/1.82  thf('34', plain,
% 1.61/1.82      (![X5 : $i, X6 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.61/1.82      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.61/1.82  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['33', '34'])).
% 1.61/1.82  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('38', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['32', '37'])).
% 1.61/1.82  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('40', plain, ((v1_pre_topc @ sk_D)),
% 1.61/1.82      inference('clc', [status(thm)], ['38', '39'])).
% 1.61/1.82  thf('41', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('43', plain,
% 1.61/1.82      (![X5 : $i, X6 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.61/1.82      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.61/1.82  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.61/1.82      inference('sup-', [status(thm)], ['42', '43'])).
% 1.61/1.82  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('47', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('48', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('49', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.61/1.82          | (m1_pre_topc @ sk_C @ X0))),
% 1.61/1.82      inference('demod', [status(thm)], ['29', '40', '41', '46', '47', '48'])).
% 1.61/1.82  thf('50', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_D)
% 1.61/1.82        | (m1_pre_topc @ sk_C @ sk_D)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_D))),
% 1.61/1.82      inference('sup-', [status(thm)], ['21', '49'])).
% 1.61/1.82  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.61/1.82  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('55', plain,
% 1.61/1.82      (((v2_struct_0 @ sk_A)
% 1.61/1.82        | (v2_struct_0 @ sk_C)
% 1.61/1.82        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.61/1.82        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_B))),
% 1.61/1.82      inference('demod', [status(thm)],
% 1.61/1.82                ['13', '14', '15', '16', '19', '20', '53', '54'])).
% 1.61/1.82  thf('56', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf('57', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('58', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v1_pre_topc @ X0)
% 1.61/1.82          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.61/1.82  thf('59', plain,
% 1.61/1.82      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X8)
% 1.61/1.82          | ~ (l1_pre_topc @ X9)
% 1.61/1.82          | (m1_pre_topc @ X9 @ X8)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 1.61/1.82          | ~ (m1_pre_topc @ X10 @ X11)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 1.61/1.82          | ~ (l1_pre_topc @ X10)
% 1.61/1.82          | ~ (l1_pre_topc @ X11))),
% 1.61/1.82      inference('cnf', [status(esa)], [t31_pre_topc])).
% 1.61/1.82  thf('60', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ X0)
% 1.61/1.82          | (m1_pre_topc @ X1 @ X2)
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X2))),
% 1.61/1.82      inference('eq_res', [status(thm)], ['59'])).
% 1.61/1.82  thf('61', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X2)
% 1.61/1.82          | (m1_pre_topc @ X1 @ X2)
% 1.61/1.82          | ~ (m1_pre_topc @ X1 @ X0)
% 1.61/1.82          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.61/1.82              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 1.61/1.82          | ~ (l1_pre_topc @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.82  thf('62', plain,
% 1.61/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.82         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X2)
% 1.61/1.82          | ~ (m1_pre_topc @ X2 @ X0)
% 1.61/1.82          | (m1_pre_topc @ X2 @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X1))),
% 1.61/1.82      inference('sup-', [status(thm)], ['58', '61'])).
% 1.61/1.82  thf('63', plain,
% 1.61/1.82      (![X1 : $i, X2 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X1)
% 1.61/1.82          | (m1_pre_topc @ X2 @ X1)
% 1.61/1.82          | ~ (m1_pre_topc @ X2 @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.61/1.82          | ~ (l1_pre_topc @ X2)
% 1.61/1.82          | ~ (v1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 1.61/1.82          | ~ (l1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 1.61/1.82      inference('simplify', [status(thm)], ['62'])).
% 1.61/1.82  thf('64', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v1_pre_topc @ sk_D)
% 1.61/1.82          | ~ (l1_pre_topc @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ 
% 1.61/1.82               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.61/1.82          | (m1_pre_topc @ X0 @ sk_C)
% 1.61/1.82          | ~ (l1_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['57', '63'])).
% 1.61/1.82  thf('65', plain, ((v1_pre_topc @ sk_D)),
% 1.61/1.82      inference('clc', [status(thm)], ['38', '39'])).
% 1.61/1.82  thf('66', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('67', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('68', plain,
% 1.61/1.82      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('69', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('70', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.61/1.82          | (m1_pre_topc @ X0 @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '69'])).
% 1.61/1.82  thf('71', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_D)
% 1.61/1.82        | (m1_pre_topc @ sk_D @ sk_C)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_D))),
% 1.61/1.82      inference('sup-', [status(thm)], ['56', '70'])).
% 1.61/1.82  thf('72', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['44', '45'])).
% 1.61/1.82  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.61/1.82  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('76', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(t4_tsep_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( m1_pre_topc @ B @ A ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( m1_pre_topc @ C @ A ) =>
% 1.61/1.82               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.61/1.82                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.61/1.82  thf('77', plain,
% 1.61/1.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X24 @ X25)
% 1.61/1.82          | ~ (m1_pre_topc @ X24 @ X26)
% 1.61/1.82          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 1.61/1.82          | ~ (m1_pre_topc @ X26 @ X25)
% 1.61/1.82          | ~ (l1_pre_topc @ X25)
% 1.61/1.82          | ~ (v2_pre_topc @ X25))),
% 1.61/1.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.61/1.82  thf('78', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ sk_A)
% 1.61/1.82          | ~ (l1_pre_topc @ sk_A)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.61/1.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['76', '77'])).
% 1.61/1.82  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('81', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.61/1.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.61/1.82      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.61/1.82  thf('82', plain,
% 1.61/1.82      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 1.61/1.82        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 1.61/1.82      inference('sup-', [status(thm)], ['75', '81'])).
% 1.61/1.82  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.61/1.82      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.61/1.82  thf('84', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 1.61/1.82      inference('demod', [status(thm)], ['82', '83'])).
% 1.61/1.82  thf(t19_tsep_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.61/1.82               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 1.61/1.82                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 1.61/1.82  thf('85', plain,
% 1.61/1.82      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.61/1.82         (~ (v1_tsep_1 @ X18 @ X19)
% 1.61/1.82          | ~ (m1_pre_topc @ X18 @ X19)
% 1.61/1.82          | ~ (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 1.61/1.82          | (v1_tsep_1 @ X18 @ X20)
% 1.61/1.82          | ~ (m1_pre_topc @ X20 @ X19)
% 1.61/1.82          | (v2_struct_0 @ X20)
% 1.61/1.82          | ~ (l1_pre_topc @ X19)
% 1.61/1.82          | ~ (v2_pre_topc @ X19)
% 1.61/1.82          | (v2_struct_0 @ X19))),
% 1.61/1.82      inference('cnf', [status(esa)], [t19_tsep_1])).
% 1.61/1.82  thf('86', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((v2_struct_0 @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | (v2_struct_0 @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.61/1.82          | (v1_tsep_1 @ sk_C @ sk_D)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.61/1.82          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['84', '85'])).
% 1.61/1.82  thf('87', plain,
% 1.61/1.82      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 1.61/1.82        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.61/1.82        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_D)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | ~ (v2_pre_topc @ sk_C)
% 1.61/1.82        | (v2_struct_0 @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['74', '86'])).
% 1.61/1.82  thf('88', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf('89', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf(fc10_tops_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.61/1.82  thf('90', plain,
% 1.61/1.82      (![X12 : $i]:
% 1.61/1.82         ((v3_pre_topc @ (k2_struct_0 @ X12) @ X12)
% 1.61/1.82          | ~ (l1_pre_topc @ X12)
% 1.61/1.82          | ~ (v2_pre_topc @ X12))),
% 1.61/1.82      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.61/1.82  thf(d3_struct_0, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.61/1.82  thf('91', plain,
% 1.61/1.82      (![X3 : $i]:
% 1.61/1.82         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 1.61/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.61/1.82  thf('92', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf(t1_tsep_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( l1_pre_topc @ A ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( m1_pre_topc @ B @ A ) =>
% 1.61/1.82           ( m1_subset_1 @
% 1.61/1.82             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.61/1.82  thf('93', plain,
% 1.61/1.82      (![X21 : $i, X22 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X21 @ X22)
% 1.61/1.82          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 1.61/1.82             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.61/1.82          | ~ (l1_pre_topc @ X22))),
% 1.61/1.82      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.61/1.82  thf('94', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.61/1.82             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.61/1.82      inference('sup-', [status(thm)], ['92', '93'])).
% 1.61/1.82  thf('95', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.61/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['94'])).
% 1.61/1.82  thf(t16_tsep_1, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]:
% 1.61/1.82         ( ( m1_pre_topc @ B @ A ) =>
% 1.61/1.82           ( ![C:$i]:
% 1.61/1.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.61/1.82               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.61/1.82                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.61/1.82                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.61/1.82  thf('96', plain,
% 1.61/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X15 @ X16)
% 1.61/1.82          | ((X17) != (u1_struct_0 @ X15))
% 1.61/1.82          | ~ (v3_pre_topc @ X17 @ X16)
% 1.61/1.82          | (v1_tsep_1 @ X15 @ X16)
% 1.61/1.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.61/1.82          | ~ (l1_pre_topc @ X16)
% 1.61/1.82          | ~ (v2_pre_topc @ X16))),
% 1.61/1.82      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.61/1.82  thf('97', plain,
% 1.61/1.82      (![X15 : $i, X16 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X16)
% 1.61/1.82          | ~ (l1_pre_topc @ X16)
% 1.61/1.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.61/1.82               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.61/1.82          | (v1_tsep_1 @ X15 @ X16)
% 1.61/1.82          | ~ (v3_pre_topc @ (u1_struct_0 @ X15) @ X16)
% 1.61/1.82          | ~ (m1_pre_topc @ X15 @ X16))),
% 1.61/1.82      inference('simplify', [status(thm)], ['96'])).
% 1.61/1.82  thf('98', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['95', '97'])).
% 1.61/1.82  thf('99', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['98'])).
% 1.61/1.82  thf('100', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['91', '99'])).
% 1.61/1.82  thf('101', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['90', '100'])).
% 1.61/1.82  thf('102', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_struct_0 @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['101'])).
% 1.61/1.82  thf('103', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['89', '102'])).
% 1.61/1.82  thf('104', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_struct_0 @ X0)
% 1.61/1.82          | (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['103'])).
% 1.61/1.82  thf('105', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.61/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['94'])).
% 1.61/1.82  thf('106', plain,
% 1.61/1.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X15 @ X16)
% 1.61/1.82          | ((X17) != (u1_struct_0 @ X15))
% 1.61/1.82          | ~ (v1_tsep_1 @ X15 @ X16)
% 1.61/1.82          | ~ (m1_pre_topc @ X15 @ X16)
% 1.61/1.82          | (v3_pre_topc @ X17 @ X16)
% 1.61/1.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.61/1.82          | ~ (l1_pre_topc @ X16)
% 1.61/1.82          | ~ (v2_pre_topc @ X16))),
% 1.61/1.82      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.61/1.82  thf('107', plain,
% 1.61/1.82      (![X15 : $i, X16 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X16)
% 1.61/1.82          | ~ (l1_pre_topc @ X16)
% 1.61/1.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.61/1.82               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.61/1.82          | (v3_pre_topc @ (u1_struct_0 @ X15) @ X16)
% 1.61/1.82          | ~ (v1_tsep_1 @ X15 @ X16)
% 1.61/1.82          | ~ (m1_pre_topc @ X15 @ X16))),
% 1.61/1.82      inference('simplify', [status(thm)], ['106'])).
% 1.61/1.82  thf('108', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['105', '107'])).
% 1.61/1.82  thf('109', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X0)
% 1.61/1.82          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['108'])).
% 1.61/1.82  thf('110', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['104', '109'])).
% 1.61/1.82  thf('111', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ X0 @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['110'])).
% 1.61/1.82  thf('112', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0)
% 1.61/1.82          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['88', '111'])).
% 1.61/1.82  thf('113', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.61/1.82          | ~ (l1_struct_0 @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['112'])).
% 1.61/1.82  thf('114', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf('115', plain,
% 1.61/1.82      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 1.61/1.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.61/1.82  thf('116', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('117', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.61/1.82          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.61/1.82      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.61/1.82  thf('118', plain,
% 1.61/1.82      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 1.61/1.82        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 1.61/1.82      inference('sup-', [status(thm)], ['116', '117'])).
% 1.61/1.82  thf('119', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 1.61/1.82      inference('sup-', [status(thm)], ['115', '118'])).
% 1.61/1.82  thf('120', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('121', plain,
% 1.61/1.82      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['119', '120'])).
% 1.61/1.82  thf('122', plain,
% 1.61/1.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X24 @ X25)
% 1.61/1.82          | ~ (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 1.61/1.82          | (m1_pre_topc @ X24 @ X26)
% 1.61/1.82          | ~ (m1_pre_topc @ X26 @ X25)
% 1.61/1.82          | ~ (l1_pre_topc @ X25)
% 1.61/1.82          | ~ (v2_pre_topc @ X25))),
% 1.61/1.82      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.61/1.82  thf('123', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.61/1.82          | (m1_pre_topc @ sk_C @ sk_C)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.61/1.82      inference('sup-', [status(thm)], ['121', '122'])).
% 1.61/1.82  thf('124', plain,
% 1.61/1.82      (![X0 : $i]:
% 1.61/1.82         ((m1_pre_topc @ sk_C @ sk_C)
% 1.61/1.82          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.61/1.82          | ~ (l1_pre_topc @ X0)
% 1.61/1.82          | ~ (v2_pre_topc @ X0))),
% 1.61/1.82      inference('simplify', [status(thm)], ['123'])).
% 1.61/1.82  thf('125', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | ~ (v2_pre_topc @ sk_C)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | (m1_pre_topc @ sk_C @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['114', '124'])).
% 1.61/1.82  thf('126', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('127', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf(cc1_pre_topc, axiom,
% 1.61/1.82    (![A:$i]:
% 1.61/1.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.61/1.82       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.61/1.82  thf('128', plain,
% 1.61/1.82      (![X1 : $i, X2 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X1 @ X2)
% 1.61/1.82          | (v2_pre_topc @ X1)
% 1.61/1.82          | ~ (l1_pre_topc @ X2)
% 1.61/1.82          | ~ (v2_pre_topc @ X2))),
% 1.61/1.82      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.61/1.82  thf('129', plain,
% 1.61/1.82      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['127', '128'])).
% 1.61/1.82  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('132', plain, ((v2_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.61/1.82  thf('133', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('134', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['125', '126', '132', '133'])).
% 1.61/1.82  thf('135', plain,
% 1.61/1.82      (![X21 : $i, X22 : $i]:
% 1.61/1.82         (~ (m1_pre_topc @ X21 @ X22)
% 1.61/1.82          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 1.61/1.82             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.61/1.82          | ~ (l1_pre_topc @ X22))),
% 1.61/1.82      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.61/1.82  thf('136', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.61/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 1.61/1.82      inference('sup-', [status(thm)], ['134', '135'])).
% 1.61/1.82  thf('137', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('138', plain,
% 1.61/1.82      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 1.61/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 1.61/1.82      inference('demod', [status(thm)], ['136', '137'])).
% 1.61/1.82  thf('139', plain,
% 1.61/1.82      (![X15 : $i, X16 : $i]:
% 1.61/1.82         (~ (v2_pre_topc @ X16)
% 1.61/1.82          | ~ (l1_pre_topc @ X16)
% 1.61/1.82          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.61/1.82               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.61/1.82          | (v1_tsep_1 @ X15 @ X16)
% 1.61/1.82          | ~ (v3_pre_topc @ (u1_struct_0 @ X15) @ X16)
% 1.61/1.82          | ~ (m1_pre_topc @ X15 @ X16))),
% 1.61/1.82      inference('simplify', [status(thm)], ['96'])).
% 1.61/1.82  thf('140', plain,
% 1.61/1.82      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 1.61/1.82        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 1.61/1.82        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.61/1.82        | ~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | ~ (v2_pre_topc @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['138', '139'])).
% 1.61/1.82  thf('141', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['125', '126', '132', '133'])).
% 1.61/1.82  thf('142', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('143', plain, ((v2_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.61/1.82  thf('144', plain,
% 1.61/1.82      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 1.61/1.82        | (v1_tsep_1 @ sk_C @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.61/1.82  thf('145', plain,
% 1.61/1.82      ((~ (l1_pre_topc @ sk_C)
% 1.61/1.82        | ~ (v2_pre_topc @ sk_C)
% 1.61/1.82        | ~ (l1_struct_0 @ sk_C)
% 1.61/1.82        | (v1_tsep_1 @ sk_C @ sk_C))),
% 1.61/1.82      inference('sup-', [status(thm)], ['113', '144'])).
% 1.61/1.82  thf('146', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('147', plain, ((v2_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.61/1.82  thf('148', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf(dt_l1_pre_topc, axiom,
% 1.61/1.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.61/1.82  thf('149', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.61/1.82      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.61/1.82  thf('150', plain, ((l1_struct_0 @ sk_C)),
% 1.61/1.82      inference('sup-', [status(thm)], ['148', '149'])).
% 1.61/1.82  thf('151', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['145', '146', '147', '150'])).
% 1.61/1.82  thf('152', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['125', '126', '132', '133'])).
% 1.61/1.82  thf('153', plain, ((l1_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['35', '36'])).
% 1.61/1.82  thf('154', plain, ((v2_pre_topc @ sk_C)),
% 1.61/1.82      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.61/1.82  thf('155', plain,
% 1.61/1.82      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.61/1.82      inference('demod', [status(thm)], ['87', '151', '152', '153', '154'])).
% 1.61/1.82  thf('156', plain, (~ (v2_struct_0 @ sk_D)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('157', plain, (((v2_struct_0 @ sk_C) | (v1_tsep_1 @ sk_C @ sk_D))),
% 1.61/1.82      inference('clc', [status(thm)], ['155', '156'])).
% 1.61/1.82  thf('158', plain, (~ (v2_struct_0 @ sk_C)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('159', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.61/1.82      inference('clc', [status(thm)], ['157', '158'])).
% 1.61/1.82  thf('160', plain,
% 1.61/1.82      (((v2_struct_0 @ sk_A)
% 1.61/1.82        | (v2_struct_0 @ sk_C)
% 1.61/1.82        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.61/1.82        | (v2_struct_0 @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_B))),
% 1.61/1.82      inference('demod', [status(thm)], ['55', '159'])).
% 1.61/1.82  thf('161', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('162', plain,
% 1.61/1.82      (((v2_struct_0 @ sk_B)
% 1.61/1.82        | (v2_struct_0 @ sk_D)
% 1.61/1.82        | (v2_struct_0 @ sk_C)
% 1.61/1.82        | (v2_struct_0 @ sk_A))),
% 1.61/1.82      inference('sup-', [status(thm)], ['160', '161'])).
% 1.61/1.82  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('164', plain,
% 1.61/1.82      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 1.61/1.82      inference('sup-', [status(thm)], ['162', '163'])).
% 1.61/1.82  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('166', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.61/1.82      inference('clc', [status(thm)], ['164', '165'])).
% 1.61/1.82  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 1.61/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.82  thf('168', plain, ((v2_struct_0 @ sk_C)),
% 1.61/1.82      inference('clc', [status(thm)], ['166', '167'])).
% 1.61/1.82  thf('169', plain, ($false), inference('demod', [status(thm)], ['0', '168'])).
% 1.61/1.82  
% 1.61/1.82  % SZS output end Refutation
% 1.61/1.82  
% 1.61/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
