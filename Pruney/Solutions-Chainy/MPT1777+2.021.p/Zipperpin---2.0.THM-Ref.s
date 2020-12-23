%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RCrcvspC0w

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:29 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  210 (1229 expanded)
%              Number of leaves         :   40 ( 366 expanded)
%              Depth                    :   27
%              Number of atoms          : 2017 (36648 expanded)
%              Number of equality atoms :   37 (1001 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( v1_tsep_1 @ X32 @ X30 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X30 ) )
      | ( X33 != X34 )
      | ~ ( r1_tmap_1 @ X32 @ X29 @ ( k3_tmap_1 @ X31 @ X29 @ X30 @ X32 @ X35 ) @ X34 )
      | ( r1_tmap_1 @ X30 @ X29 @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X30 @ X29 @ X35 @ X34 )
      | ~ ( r1_tmap_1 @ X32 @ X29 @ ( k3_tmap_1 @ X31 @ X29 @ X30 @ X32 @ X35 ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ~ ( v1_tsep_1 @ X32 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('63',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('64',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('66',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['61','62','63','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v3_pre_topc @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('81',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('82',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('83',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
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
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    v1_pre_topc @ sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('92',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('94',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['82','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('99',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('102',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('103',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('104',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('106',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('116',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['29','40','41','46','47','48'])).

thf('125',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('127',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('131',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('133',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126'])).

thf('135',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('136',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('138',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['133','134','135','141'])).

thf('143',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['122','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('145',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('146',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('147',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('148',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['143','144','145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('153',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['125','126'])).

thf('154',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('155',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['79','80','81','100','155'])).

thf('157',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['70','156'])).

thf('158',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','53','157','158'])).

thf('160',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['0','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RCrcvspC0w
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:02:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.89/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.11  % Solved by: fo/fo7.sh
% 0.89/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.11  % done 1445 iterations in 0.637s
% 0.89/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.11  % SZS output start Refutation
% 0.89/1.11  thf(sk_G_type, type, sk_G: $i).
% 0.89/1.11  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.89/1.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.11  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.11  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.89/1.11  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.11  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.89/1.11  thf(sk_F_type, type, sk_F: $i).
% 0.89/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.11  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.89/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.11  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.89/1.11  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.89/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.89/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.11  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.89/1.11  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.89/1.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.11  thf(t88_tmap_1, conjecture,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.11             ( l1_pre_topc @ B ) ) =>
% 0.89/1.11           ( ![C:$i]:
% 0.89/1.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.89/1.11               ( ![D:$i]:
% 0.89/1.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.89/1.11                   ( ![E:$i]:
% 0.89/1.11                     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.11                         ( v1_funct_2 @
% 0.89/1.11                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.11                         ( m1_subset_1 @
% 0.89/1.11                           E @ 
% 0.89/1.11                           ( k1_zfmisc_1 @
% 0.89/1.11                             ( k2_zfmisc_1 @
% 0.89/1.11                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.11                       ( ( ( g1_pre_topc @
% 0.89/1.11                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.89/1.11                           ( D ) ) =>
% 0.89/1.11                         ( ![F:$i]:
% 0.89/1.11                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.89/1.11                             ( ![G:$i]:
% 0.89/1.11                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.89/1.11                                 ( ( ( ( F ) = ( G ) ) & 
% 0.89/1.11                                     ( r1_tmap_1 @
% 0.89/1.11                                       C @ B @ 
% 0.89/1.11                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.89/1.11                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.11    (~( ![A:$i]:
% 0.89/1.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.11            ( l1_pre_topc @ A ) ) =>
% 0.89/1.11          ( ![B:$i]:
% 0.89/1.11            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.11                ( l1_pre_topc @ B ) ) =>
% 0.89/1.11              ( ![C:$i]:
% 0.89/1.11                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.89/1.11                  ( ![D:$i]:
% 0.89/1.11                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.89/1.11                      ( ![E:$i]:
% 0.89/1.11                        ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.11                            ( v1_funct_2 @
% 0.89/1.11                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.11                            ( m1_subset_1 @
% 0.89/1.11                              E @ 
% 0.89/1.11                              ( k1_zfmisc_1 @
% 0.89/1.11                                ( k2_zfmisc_1 @
% 0.89/1.11                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.11                          ( ( ( g1_pre_topc @
% 0.89/1.11                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.89/1.11                              ( D ) ) =>
% 0.89/1.11                            ( ![F:$i]:
% 0.89/1.11                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.89/1.11                                ( ![G:$i]:
% 0.89/1.11                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.89/1.11                                    ( ( ( ( F ) = ( G ) ) & 
% 0.89/1.11                                        ( r1_tmap_1 @
% 0.89/1.11                                          C @ B @ 
% 0.89/1.11                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.89/1.11                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.89/1.11    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.89/1.11  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('1', plain,
% 0.89/1.11      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.89/1.11        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('2', plain, (((sk_F) = (sk_G))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('3', plain,
% 0.89/1.11      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.89/1.11        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.89/1.11      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.11  thf('4', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_E @ 
% 0.89/1.11        (k1_zfmisc_1 @ 
% 0.89/1.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t86_tmap_1, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.11             ( l1_pre_topc @ B ) ) =>
% 0.89/1.11           ( ![C:$i]:
% 0.89/1.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.89/1.11               ( ![D:$i]:
% 0.89/1.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.89/1.11                   ( ![E:$i]:
% 0.89/1.11                     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.11                         ( v1_funct_2 @
% 0.89/1.11                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.11                         ( m1_subset_1 @
% 0.89/1.11                           E @ 
% 0.89/1.11                           ( k1_zfmisc_1 @
% 0.89/1.11                             ( k2_zfmisc_1 @
% 0.89/1.11                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.11                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.89/1.11                         ( ![F:$i]:
% 0.89/1.11                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.89/1.11                             ( ![G:$i]:
% 0.89/1.11                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.89/1.11                                 ( ( ( F ) = ( G ) ) =>
% 0.89/1.11                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.89/1.11                                     ( r1_tmap_1 @
% 0.89/1.11                                       C @ B @ 
% 0.89/1.11                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf('5', plain,
% 0.89/1.11      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.11         ((v2_struct_0 @ X29)
% 0.89/1.11          | ~ (v2_pre_topc @ X29)
% 0.89/1.11          | ~ (l1_pre_topc @ X29)
% 0.89/1.11          | (v2_struct_0 @ X30)
% 0.89/1.11          | ~ (m1_pre_topc @ X30 @ X31)
% 0.89/1.11          | ~ (v1_tsep_1 @ X32 @ X30)
% 0.89/1.11          | ~ (m1_pre_topc @ X32 @ X30)
% 0.89/1.11          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X30))
% 0.89/1.11          | ((X33) != (X34))
% 0.89/1.11          | ~ (r1_tmap_1 @ X32 @ X29 @ 
% 0.89/1.11               (k3_tmap_1 @ X31 @ X29 @ X30 @ X32 @ X35) @ X34)
% 0.89/1.11          | (r1_tmap_1 @ X30 @ X29 @ X35 @ X33)
% 0.89/1.11          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 0.89/1.11          | ~ (m1_subset_1 @ X35 @ 
% 0.89/1.11               (k1_zfmisc_1 @ 
% 0.89/1.11                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.89/1.11          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.89/1.11          | ~ (v1_funct_1 @ X35)
% 0.89/1.11          | ~ (m1_pre_topc @ X32 @ X31)
% 0.89/1.11          | (v2_struct_0 @ X32)
% 0.89/1.11          | ~ (l1_pre_topc @ X31)
% 0.89/1.11          | ~ (v2_pre_topc @ X31)
% 0.89/1.11          | (v2_struct_0 @ X31))),
% 0.89/1.11      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.89/1.11  thf('6', plain,
% 0.89/1.11      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X34 : $i, X35 : $i]:
% 0.89/1.11         ((v2_struct_0 @ X31)
% 0.89/1.11          | ~ (v2_pre_topc @ X31)
% 0.89/1.11          | ~ (l1_pre_topc @ X31)
% 0.89/1.11          | (v2_struct_0 @ X32)
% 0.89/1.11          | ~ (m1_pre_topc @ X32 @ X31)
% 0.89/1.11          | ~ (v1_funct_1 @ X35)
% 0.89/1.11          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.89/1.11          | ~ (m1_subset_1 @ X35 @ 
% 0.89/1.11               (k1_zfmisc_1 @ 
% 0.89/1.11                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.89/1.11          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 0.89/1.11          | (r1_tmap_1 @ X30 @ X29 @ X35 @ X34)
% 0.89/1.11          | ~ (r1_tmap_1 @ X32 @ X29 @ 
% 0.89/1.11               (k3_tmap_1 @ X31 @ X29 @ X30 @ X32 @ X35) @ X34)
% 0.89/1.11          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X30))
% 0.89/1.11          | ~ (m1_pre_topc @ X32 @ X30)
% 0.89/1.11          | ~ (v1_tsep_1 @ X32 @ X30)
% 0.89/1.11          | ~ (m1_pre_topc @ X30 @ X31)
% 0.89/1.11          | (v2_struct_0 @ X30)
% 0.89/1.11          | ~ (l1_pre_topc @ X29)
% 0.89/1.11          | ~ (v2_pre_topc @ X29)
% 0.89/1.11          | (v2_struct_0 @ X29))),
% 0.89/1.11      inference('simplify', [status(thm)], ['5'])).
% 0.89/1.11  thf('7', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((v2_struct_0 @ sk_B)
% 0.89/1.11          | ~ (v2_pre_topc @ sk_B)
% 0.89/1.11          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.11          | (v2_struct_0 @ sk_D)
% 0.89/1.11          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.89/1.11          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.89/1.11          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.89/1.11          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.89/1.11          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.89/1.11               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.89/1.11          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.89/1.11          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.89/1.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.89/1.11          | ~ (v1_funct_1 @ sk_E)
% 0.89/1.11          | ~ (m1_pre_topc @ X1 @ X0)
% 0.89/1.11          | (v2_struct_0 @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (v2_pre_topc @ X0)
% 0.89/1.11          | (v2_struct_0 @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['4', '6'])).
% 0.89/1.11  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('10', plain,
% 0.89/1.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('12', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((v2_struct_0 @ sk_B)
% 0.89/1.11          | (v2_struct_0 @ sk_D)
% 0.89/1.11          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.89/1.11          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.89/1.11          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.89/1.11          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.89/1.11          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.89/1.11               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.89/1.11          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.89/1.11          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.89/1.11          | ~ (m1_pre_topc @ X1 @ X0)
% 0.89/1.11          | (v2_struct_0 @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (v2_pre_topc @ X0)
% 0.89/1.11          | (v2_struct_0 @ X0))),
% 0.89/1.11      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.89/1.11  thf('13', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | (v2_struct_0 @ sk_C)
% 0.89/1.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.89/1.11        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.89/1.11        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.89/1.11        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.89/1.11        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.89/1.11        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.89/1.11        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.89/1.11        | (v2_struct_0 @ sk_D)
% 0.89/1.11        | (v2_struct_0 @ sk_B))),
% 0.89/1.11      inference('sup-', [status(thm)], ['3', '12'])).
% 0.89/1.11  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('18', plain, (((sk_F) = (sk_G))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.89/1.11      inference('demod', [status(thm)], ['17', '18'])).
% 0.89/1.11  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t2_tsep_1, axiom,
% 0.89/1.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.89/1.11  thf('21', plain,
% 0.89/1.11      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.11  thf('22', plain,
% 0.89/1.11      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(abstractness_v1_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ( v1_pre_topc @ A ) =>
% 0.89/1.11         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.89/1.11  thf('23', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (v1_pre_topc @ X0)
% 0.89/1.11          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.11          | ~ (l1_pre_topc @ X0))),
% 0.89/1.11      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.89/1.11  thf(t31_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( l1_pre_topc @ B ) =>
% 0.89/1.11           ( ![C:$i]:
% 0.89/1.11             ( ( l1_pre_topc @ C ) =>
% 0.89/1.11               ( ![D:$i]:
% 0.89/1.11                 ( ( l1_pre_topc @ D ) =>
% 0.89/1.11                   ( ( ( ( g1_pre_topc @
% 0.89/1.11                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.89/1.11                         ( g1_pre_topc @
% 0.89/1.11                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.89/1.11                       ( ( g1_pre_topc @
% 0.89/1.11                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.89/1.11                         ( g1_pre_topc @
% 0.89/1.11                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.89/1.11                       ( m1_pre_topc @ C @ A ) ) =>
% 0.89/1.11                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf('24', plain,
% 0.89/1.11      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X8)
% 0.89/1.11          | ~ (l1_pre_topc @ X9)
% 0.89/1.11          | (m1_pre_topc @ X9 @ X8)
% 0.89/1.11          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.89/1.11              != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.89/1.11          | ~ (m1_pre_topc @ X10 @ X11)
% 0.89/1.11          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.89/1.11              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.89/1.11          | ~ (l1_pre_topc @ X10)
% 0.89/1.11          | ~ (l1_pre_topc @ X11))),
% 0.89/1.11      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.89/1.11  thf('25', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.11         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (v1_pre_topc @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ X2)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.89/1.11              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.89/1.11          | ~ (m1_pre_topc @ X0 @ X2)
% 0.89/1.11          | (m1_pre_topc @ X1 @ X3)
% 0.89/1.11          | ~ (l1_pre_topc @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X3))),
% 0.89/1.11      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.11  thf('26', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X3)
% 0.89/1.11          | ~ (l1_pre_topc @ X1)
% 0.89/1.11          | (m1_pre_topc @ X1 @ X3)
% 0.89/1.11          | ~ (m1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X2)
% 0.89/1.11          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.89/1.11              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.89/1.11          | ~ (l1_pre_topc @ X2)
% 0.89/1.11          | ~ (v1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.89/1.11          | ~ (l1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('27', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ 
% 0.89/1.11             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.11          | ~ (v1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.11          | ~ (l1_pre_topc @ X1)
% 0.89/1.11          | ~ (m1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.89/1.11          | (m1_pre_topc @ X0 @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ X1))),
% 0.89/1.11      inference('eq_res', [status(thm)], ['26'])).
% 0.89/1.11  thf('28', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X0)
% 0.89/1.11          | (m1_pre_topc @ X0 @ X1)
% 0.89/1.11          | ~ (m1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X1)
% 0.89/1.11          | ~ (v1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.11          | ~ (l1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.89/1.11      inference('simplify', [status(thm)], ['27'])).
% 0.89/1.11  thf('29', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (v1_pre_topc @ sk_D)
% 0.89/1.11          | ~ (l1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (m1_pre_topc @ 
% 0.89/1.11               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.89/1.11          | (m1_pre_topc @ sk_C @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ sk_C))),
% 0.89/1.11      inference('sup-', [status(thm)], ['22', '28'])).
% 0.89/1.11  thf('30', plain,
% 0.89/1.11      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(fc7_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ( ~( v2_struct_0 @
% 0.89/1.11              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.89/1.11         ( v1_pre_topc @
% 0.89/1.11           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.89/1.11  thf('31', plain,
% 0.89/1.11      (![X7 : $i]:
% 0.89/1.11         ((v1_pre_topc @ 
% 0.89/1.11           (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.89/1.11          | ~ (l1_pre_topc @ X7)
% 0.89/1.11          | (v2_struct_0 @ X7))),
% 0.89/1.11      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.89/1.11  thf('32', plain,
% 0.89/1.11      (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.89/1.11      inference('sup+', [status(thm)], ['30', '31'])).
% 0.89/1.11  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(dt_m1_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.89/1.11  thf('34', plain,
% 0.89/1.11      (![X5 : $i, X6 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.89/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.89/1.11  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.89/1.11      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.11  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.11      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.11  thf('38', plain, (((v1_pre_topc @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.89/1.11      inference('demod', [status(thm)], ['32', '37'])).
% 0.89/1.11  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('40', plain, ((v1_pre_topc @ sk_D)),
% 0.89/1.11      inference('clc', [status(thm)], ['38', '39'])).
% 0.89/1.11  thf('41', plain,
% 0.89/1.11      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('43', plain,
% 0.89/1.11      (![X5 : $i, X6 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.89/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.89/1.11  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.89/1.11      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.11  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.11  thf('47', plain,
% 0.89/1.11      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('48', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.11      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.11  thf('49', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.89/1.11          | (m1_pre_topc @ sk_C @ X0))),
% 0.89/1.11      inference('demod', [status(thm)], ['29', '40', '41', '46', '47', '48'])).
% 0.89/1.11  thf('50', plain,
% 0.89/1.11      ((~ (l1_pre_topc @ sk_D)
% 0.89/1.11        | (m1_pre_topc @ sk_C @ sk_D)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_D))),
% 0.89/1.11      inference('sup-', [status(thm)], ['21', '49'])).
% 0.89/1.11  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.11  thf('52', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.11  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.89/1.11  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.89/1.11  thf(t1_tsep_1, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_pre_topc @ B @ A ) =>
% 0.89/1.11           ( m1_subset_1 @
% 0.89/1.11             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.89/1.11  thf('55', plain,
% 0.89/1.11      (![X23 : $i, X24 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X23 @ X24)
% 0.89/1.11          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.89/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.89/1.11          | ~ (l1_pre_topc @ X24))),
% 0.89/1.11      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.89/1.11  thf('56', plain,
% 0.89/1.11      ((~ (l1_pre_topc @ sk_D)
% 0.89/1.11        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.11           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.89/1.11      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.11  thf('57', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.11  thf('58', plain,
% 0.89/1.11      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.89/1.11      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.11  thf(t16_tsep_1, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_pre_topc @ B @ A ) =>
% 0.89/1.11           ( ![C:$i]:
% 0.89/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.89/1.11                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.89/1.11                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf('59', plain,
% 0.89/1.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X20 @ X21)
% 0.89/1.11          | ((X22) != (u1_struct_0 @ X20))
% 0.89/1.11          | ~ (v3_pre_topc @ X22 @ X21)
% 0.89/1.11          | (v1_tsep_1 @ X20 @ X21)
% 0.89/1.11          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.11          | ~ (l1_pre_topc @ X21)
% 0.89/1.11          | ~ (v2_pre_topc @ X21))),
% 0.89/1.11      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.89/1.11  thf('60', plain,
% 0.89/1.11      (![X20 : $i, X21 : $i]:
% 0.89/1.11         (~ (v2_pre_topc @ X21)
% 0.89/1.11          | ~ (l1_pre_topc @ X21)
% 0.89/1.11          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.89/1.11               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.11          | (v1_tsep_1 @ X20 @ X21)
% 0.89/1.11          | ~ (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.89/1.11          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.89/1.11      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.11  thf('61', plain,
% 0.89/1.11      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.89/1.11        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.89/1.11        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_D)
% 0.89/1.11        | ~ (v2_pre_topc @ sk_D))),
% 0.89/1.11      inference('sup-', [status(thm)], ['58', '60'])).
% 0.89/1.11  thf('62', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.89/1.11  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.11  thf('64', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(cc1_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.89/1.11  thf('65', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X1 @ X2)
% 0.89/1.11          | (v2_pre_topc @ X1)
% 0.89/1.11          | ~ (l1_pre_topc @ X2)
% 0.89/1.11          | ~ (v2_pre_topc @ X2))),
% 0.89/1.11      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.89/1.11  thf('66', plain,
% 0.89/1.11      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.89/1.11      inference('sup-', [status(thm)], ['64', '65'])).
% 0.89/1.11  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('69', plain, ((v2_pre_topc @ sk_D)),
% 0.89/1.11      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.89/1.11  thf('70', plain,
% 0.89/1.11      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.89/1.11        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.89/1.11      inference('demod', [status(thm)], ['61', '62', '63', '69'])).
% 0.89/1.11  thf('71', plain,
% 0.89/1.11      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.11  thf('72', plain,
% 0.89/1.11      (![X23 : $i, X24 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X23 @ X24)
% 0.89/1.11          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.89/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.89/1.11          | ~ (l1_pre_topc @ X24))),
% 0.89/1.11      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.89/1.11  thf('73', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.89/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.89/1.11      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.11  thf('74', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.89/1.11           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.11          | ~ (l1_pre_topc @ X0))),
% 0.89/1.11      inference('simplify', [status(thm)], ['73'])).
% 0.89/1.11  thf('75', plain,
% 0.89/1.11      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.89/1.11      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.11  thf(t33_tops_2, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.12     ( ( l1_pre_topc @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ![C:$i]:
% 0.89/1.12             ( ( m1_pre_topc @ C @ A ) =>
% 0.89/1.12               ( ( v3_pre_topc @ B @ A ) =>
% 0.89/1.12                 ( ![D:$i]:
% 0.89/1.12                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.89/1.12                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.12  thf('76', plain,
% 0.89/1.12      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.89/1.12          | ~ (v3_pre_topc @ X16 @ X17)
% 0.89/1.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.89/1.12          | (v3_pre_topc @ X18 @ X19)
% 0.89/1.12          | ((X18) != (X16))
% 0.89/1.12          | ~ (m1_pre_topc @ X19 @ X17)
% 0.89/1.12          | ~ (l1_pre_topc @ X17))),
% 0.89/1.12      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.89/1.12  thf('77', plain,
% 0.89/1.12      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X17)
% 0.89/1.12          | ~ (m1_pre_topc @ X19 @ X17)
% 0.89/1.12          | (v3_pre_topc @ X16 @ X19)
% 0.89/1.12          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.89/1.12          | ~ (v3_pre_topc @ X16 @ X17)
% 0.89/1.12          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.12  thf('78', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.12          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.89/1.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['75', '77'])).
% 0.89/1.12  thf('79', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | ~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.89/1.12        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.89/1.12        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['74', '78'])).
% 0.89/1.12  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('81', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('82', plain,
% 0.89/1.12      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.12      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.12  thf('83', plain,
% 0.89/1.12      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('84', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_pre_topc @ X0)
% 0.89/1.12          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.89/1.12  thf('85', plain,
% 0.89/1.12      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X8)
% 0.89/1.12          | ~ (l1_pre_topc @ X9)
% 0.89/1.12          | (m1_pre_topc @ X9 @ X8)
% 0.89/1.12          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.89/1.12              != (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.89/1.12          | ~ (m1_pre_topc @ X10 @ X11)
% 0.89/1.12          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.89/1.12              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.89/1.12          | ~ (l1_pre_topc @ X10)
% 0.89/1.12          | ~ (l1_pre_topc @ X11))),
% 0.89/1.12      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.89/1.12  thf('86', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X1)
% 0.89/1.12          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.89/1.12              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.89/1.12          | ~ (m1_pre_topc @ X1 @ X0)
% 0.89/1.12          | (m1_pre_topc @ X1 @ X2)
% 0.89/1.12          | ~ (l1_pre_topc @ X1)
% 0.89/1.12          | ~ (l1_pre_topc @ X2))),
% 0.89/1.12      inference('eq_res', [status(thm)], ['85'])).
% 0.89/1.12  thf('87', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X2)
% 0.89/1.12          | (m1_pre_topc @ X1 @ X2)
% 0.89/1.12          | ~ (m1_pre_topc @ X1 @ X0)
% 0.89/1.12          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.89/1.12              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.89/1.12          | ~ (l1_pre_topc @ X1)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['86'])).
% 0.89/1.12  thf('88', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v1_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X2)
% 0.89/1.12          | ~ (m1_pre_topc @ X2 @ X0)
% 0.89/1.12          | (m1_pre_topc @ X2 @ X1)
% 0.89/1.12          | ~ (l1_pre_topc @ X1))),
% 0.89/1.12      inference('sup-', [status(thm)], ['84', '87'])).
% 0.89/1.12  thf('89', plain,
% 0.89/1.12      (![X1 : $i, X2 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X1)
% 0.89/1.12          | (m1_pre_topc @ X2 @ X1)
% 0.89/1.12          | ~ (m1_pre_topc @ X2 @ 
% 0.89/1.12               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.89/1.12          | ~ (l1_pre_topc @ X2)
% 0.89/1.12          | ~ (v1_pre_topc @ 
% 0.89/1.12               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.89/1.12          | ~ (l1_pre_topc @ 
% 0.89/1.12               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['88'])).
% 0.89/1.12  thf('90', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v1_pre_topc @ sk_D)
% 0.89/1.12          | ~ (l1_pre_topc @ 
% 0.89/1.12               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ 
% 0.89/1.12               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.89/1.12          | (m1_pre_topc @ X0 @ sk_C)
% 0.89/1.12          | ~ (l1_pre_topc @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['83', '89'])).
% 0.89/1.12  thf('91', plain, ((v1_pre_topc @ sk_D)),
% 0.89/1.12      inference('clc', [status(thm)], ['38', '39'])).
% 0.89/1.12  thf('92', plain,
% 0.89/1.12      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.12      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.12  thf('94', plain,
% 0.89/1.12      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('95', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('96', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.89/1.12          | (m1_pre_topc @ X0 @ sk_C))),
% 0.89/1.12      inference('demod', [status(thm)], ['90', '91', '92', '93', '94', '95'])).
% 0.89/1.12  thf('97', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_D)
% 0.89/1.12        | (m1_pre_topc @ sk_D @ sk_C)
% 0.89/1.12        | ~ (l1_pre_topc @ sk_D))),
% 0.89/1.12      inference('sup-', [status(thm)], ['82', '96'])).
% 0.89/1.12  thf('98', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.12      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.12  thf('99', plain, ((l1_pre_topc @ sk_D)),
% 0.89/1.12      inference('demod', [status(thm)], ['44', '45'])).
% 0.89/1.12  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.89/1.12  thf('101', plain,
% 0.89/1.12      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.12      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.12  thf('102', plain,
% 0.89/1.12      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.12      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.89/1.12  thf(fc10_tops_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.12       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.89/1.12  thf('103', plain,
% 0.89/1.12      (![X15 : $i]:
% 0.89/1.12         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.89/1.12          | ~ (l1_pre_topc @ X15)
% 0.89/1.12          | ~ (v2_pre_topc @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.89/1.12  thf(d3_struct_0, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.89/1.12  thf('104', plain,
% 0.89/1.12      (![X3 : $i]:
% 0.89/1.12         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.89/1.12      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.12  thf('105', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['73'])).
% 0.89/1.12  thf('106', plain,
% 0.89/1.12      (![X20 : $i, X21 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X21)
% 0.89/1.12          | ~ (l1_pre_topc @ X21)
% 0.89/1.12          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.89/1.12               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.12          | (v1_tsep_1 @ X20 @ X21)
% 0.89/1.12          | ~ (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.89/1.12          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.89/1.12      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.12  thf('107', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['105', '106'])).
% 0.89/1.12  thf('108', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.12  thf('109', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['104', '108'])).
% 0.89/1.12  thf('110', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['103', '109'])).
% 0.89/1.12  thf('111', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_struct_0 @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['110'])).
% 0.89/1.12  thf('112', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['102', '111'])).
% 0.89/1.12  thf('113', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_struct_0 @ X0)
% 0.89/1.12          | (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['112'])).
% 0.89/1.12  thf('114', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.89/1.12           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['73'])).
% 0.89/1.12  thf('115', plain,
% 0.89/1.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.12         (~ (m1_pre_topc @ X20 @ X21)
% 0.89/1.12          | ((X22) != (u1_struct_0 @ X20))
% 0.89/1.12          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.89/1.12          | ~ (m1_pre_topc @ X20 @ X21)
% 0.89/1.12          | (v3_pre_topc @ X22 @ X21)
% 0.89/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.12          | ~ (l1_pre_topc @ X21)
% 0.89/1.12          | ~ (v2_pre_topc @ X21))),
% 0.89/1.12      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.89/1.12  thf('116', plain,
% 0.89/1.12      (![X20 : $i, X21 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X21)
% 0.89/1.12          | ~ (l1_pre_topc @ X21)
% 0.89/1.12          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.89/1.12               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.89/1.12          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.89/1.12          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.89/1.12      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.12  thf('117', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['114', '116'])).
% 0.89/1.12  thf('118', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['117'])).
% 0.89/1.12  thf('119', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['113', '118'])).
% 0.89/1.12  thf('120', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['119'])).
% 0.89/1.12  thf('121', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['101', '120'])).
% 0.89/1.12  thf('122', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (l1_struct_0 @ X0)
% 0.89/1.12          | ~ (v2_pre_topc @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['121'])).
% 0.89/1.12  thf('123', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.89/1.12  thf('124', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.89/1.12          | (m1_pre_topc @ sk_C @ X0))),
% 0.89/1.12      inference('demod', [status(thm)], ['29', '40', '41', '46', '47', '48'])).
% 0.89/1.12  thf('125', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['123', '124'])).
% 0.89/1.12  thf('126', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('127', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['125', '126'])).
% 0.89/1.12  thf('128', plain,
% 0.89/1.12      (![X23 : $i, X24 : $i]:
% 0.89/1.12         (~ (m1_pre_topc @ X23 @ X24)
% 0.89/1.12          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.89/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.89/1.12          | ~ (l1_pre_topc @ X24))),
% 0.89/1.12      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.89/1.12  thf('129', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.12           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['127', '128'])).
% 0.89/1.12  thf('130', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('131', plain,
% 0.89/1.12      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.89/1.12      inference('demod', [status(thm)], ['129', '130'])).
% 0.89/1.12  thf('132', plain,
% 0.89/1.12      (![X20 : $i, X21 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X21)
% 0.89/1.12          | ~ (l1_pre_topc @ X21)
% 0.89/1.12          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.89/1.12               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.12          | (v1_tsep_1 @ X20 @ X21)
% 0.89/1.12          | ~ (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.89/1.12          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.89/1.12      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.12  thf('133', plain,
% 0.89/1.12      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 0.89/1.12        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.89/1.12        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.89/1.12        | ~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | ~ (v2_pre_topc @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['131', '132'])).
% 0.89/1.12  thf('134', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['125', '126'])).
% 0.89/1.12  thf('135', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('136', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('137', plain,
% 0.89/1.12      (![X1 : $i, X2 : $i]:
% 0.89/1.12         (~ (m1_pre_topc @ X1 @ X2)
% 0.89/1.12          | (v2_pre_topc @ X1)
% 0.89/1.12          | ~ (l1_pre_topc @ X2)
% 0.89/1.12          | ~ (v2_pre_topc @ X2))),
% 0.89/1.12      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.89/1.12  thf('138', plain,
% 0.89/1.12      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['136', '137'])).
% 0.89/1.12  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('141', plain, ((v2_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.89/1.12  thf('142', plain,
% 0.89/1.12      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.89/1.12        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.89/1.12      inference('demod', [status(thm)], ['133', '134', '135', '141'])).
% 0.89/1.12  thf('143', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | ~ (v2_pre_topc @ sk_C)
% 0.89/1.12        | ~ (l1_struct_0 @ sk_C)
% 0.89/1.12        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['122', '142'])).
% 0.89/1.12  thf('144', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('145', plain, ((v2_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.89/1.12  thf('146', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf(dt_l1_pre_topc, axiom,
% 0.89/1.12    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.89/1.12  thf('147', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.12  thf('148', plain, ((l1_struct_0 @ sk_C)),
% 0.89/1.12      inference('sup-', [status(thm)], ['146', '147'])).
% 0.89/1.12  thf('149', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['143', '144', '145', '148'])).
% 0.89/1.12  thf('150', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (~ (v2_pre_topc @ X0)
% 0.89/1.12          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.12          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.89/1.12          | ~ (m1_pre_topc @ X0 @ X0)
% 0.89/1.12          | ~ (l1_pre_topc @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['117'])).
% 0.89/1.12  thf('151', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.12        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.89/1.12        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.89/1.12        | ~ (v2_pre_topc @ sk_C))),
% 0.89/1.12      inference('sup-', [status(thm)], ['149', '150'])).
% 0.89/1.12  thf('152', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('153', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['125', '126'])).
% 0.89/1.12  thf('154', plain, ((v2_pre_topc @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.89/1.12  thf('155', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)),
% 0.89/1.12      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.89/1.12  thf('156', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.89/1.12      inference('demod', [status(thm)], ['79', '80', '81', '100', '155'])).
% 0.89/1.12  thf('157', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.89/1.12      inference('demod', [status(thm)], ['70', '156'])).
% 0.89/1.12  thf('158', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('159', plain,
% 0.89/1.12      (((v2_struct_0 @ sk_A)
% 0.89/1.12        | (v2_struct_0 @ sk_C)
% 0.89/1.12        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.89/1.12        | (v2_struct_0 @ sk_D)
% 0.89/1.12        | (v2_struct_0 @ sk_B))),
% 0.89/1.12      inference('demod', [status(thm)],
% 0.89/1.12                ['13', '14', '15', '16', '19', '20', '53', '157', '158'])).
% 0.89/1.12  thf('160', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('161', plain,
% 0.89/1.12      (((v2_struct_0 @ sk_B)
% 0.89/1.12        | (v2_struct_0 @ sk_D)
% 0.89/1.12        | (v2_struct_0 @ sk_C)
% 0.89/1.12        | (v2_struct_0 @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['159', '160'])).
% 0.89/1.12  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('163', plain,
% 0.89/1.12      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.89/1.12      inference('sup-', [status(thm)], ['161', '162'])).
% 0.89/1.12  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('165', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.89/1.12      inference('clc', [status(thm)], ['163', '164'])).
% 0.89/1.12  thf('166', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('167', plain, ((v2_struct_0 @ sk_C)),
% 0.89/1.12      inference('clc', [status(thm)], ['165', '166'])).
% 0.89/1.12  thf('168', plain, ($false), inference('demod', [status(thm)], ['0', '167'])).
% 0.89/1.12  
% 0.89/1.12  % SZS output end Refutation
% 0.89/1.12  
% 0.89/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
