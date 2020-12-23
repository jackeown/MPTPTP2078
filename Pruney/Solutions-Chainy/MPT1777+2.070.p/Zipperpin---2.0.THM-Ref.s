%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FKQPAXoASu

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 281 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          : 1260 (7735 expanded)
%              Number of equality atoms :   15 ( 193 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X33 )
      | ( X33 != X31 )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ~ ( v3_pre_topc @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v3_pre_topc @ X30 @ X27 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','29','41','42'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('63',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['50','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('77',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('79',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('81',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','70','83'])).

thf('85',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('88',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','91','92'])).

thf('94',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FKQPAXoASu
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 453 iterations in 0.143s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.59  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(t88_tmap_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59             ( l1_pre_topc @ B ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.59               ( ![D:$i]:
% 0.38/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.59                   ( ![E:$i]:
% 0.38/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.59                         ( v1_funct_2 @
% 0.38/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.59                         ( m1_subset_1 @
% 0.38/0.59                           E @ 
% 0.38/0.59                           ( k1_zfmisc_1 @
% 0.38/0.59                             ( k2_zfmisc_1 @
% 0.38/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.59                       ( ( ( g1_pre_topc @
% 0.38/0.59                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.59                           ( D ) ) =>
% 0.38/0.59                         ( ![F:$i]:
% 0.38/0.59                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                             ( ![G:$i]:
% 0.38/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.59                                 ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.59                                     ( r1_tmap_1 @
% 0.38/0.59                                       C @ B @ 
% 0.38/0.59                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.59                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59            ( l1_pre_topc @ A ) ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59                ( l1_pre_topc @ B ) ) =>
% 0.38/0.59              ( ![C:$i]:
% 0.38/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.59                  ( ![D:$i]:
% 0.38/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.59                      ( ![E:$i]:
% 0.38/0.59                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.59                            ( v1_funct_2 @
% 0.38/0.59                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.59                            ( m1_subset_1 @
% 0.38/0.59                              E @ 
% 0.38/0.59                              ( k1_zfmisc_1 @
% 0.38/0.59                                ( k2_zfmisc_1 @
% 0.38/0.59                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.59                          ( ( ( g1_pre_topc @
% 0.38/0.59                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.38/0.59                              ( D ) ) =>
% 0.38/0.59                            ( ![F:$i]:
% 0.38/0.59                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                                ( ![G:$i]:
% 0.38/0.59                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.59                                    ( ( ( ( F ) = ( G ) ) & 
% 0.38/0.59                                        ( r1_tmap_1 @
% 0.38/0.59                                          C @ B @ 
% 0.38/0.59                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.38/0.59                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.38/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(fc10_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X19 : $i]:
% 0.38/0.59         ((v3_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.38/0.59          | ~ (l1_pre_topc @ X19)
% 0.38/0.59          | ~ (v2_pre_topc @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.38/0.59  thf(d3_struct_0, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X10 : $i]:
% 0.38/0.59         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.59  thf(t2_tsep_1, axiom,
% 0.38/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.59  thf(t1_tsep_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.59           ( m1_subset_1 @
% 0.38/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X20 @ X21)
% 0.38/0.59          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.38/0.59          | ~ (l1_pre_topc @ X21))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.59          | ~ (l1_pre_topc @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.59          | ~ (l1_struct_0 @ X0)
% 0.38/0.59          | ~ (l1_pre_topc @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['2', '6'])).
% 0.38/0.59  thf(dt_l1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.59  thf('8', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.38/0.59        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('11', plain, (((sk_F) = (sk_G))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.38/0.59        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.38/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_E @ 
% 0.38/0.59        (k1_zfmisc_1 @ 
% 0.38/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t84_tmap_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59             ( l1_pre_topc @ B ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.59               ( ![D:$i]:
% 0.38/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.59                   ( ![E:$i]:
% 0.38/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.59                         ( v1_funct_2 @
% 0.38/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.59                         ( m1_subset_1 @
% 0.38/0.59                           E @ 
% 0.38/0.59                           ( k1_zfmisc_1 @
% 0.38/0.59                             ( k2_zfmisc_1 @
% 0.38/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.59                       ( ( m1_pre_topc @ C @ D ) =>
% 0.38/0.59                         ( ![F:$i]:
% 0.38/0.59                           ( ( m1_subset_1 @
% 0.38/0.59                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.38/0.59                             ( ![G:$i]:
% 0.38/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                                 ( ![H:$i]:
% 0.38/0.59                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.59                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.38/0.59                                         ( r2_hidden @ G @ F ) & 
% 0.38/0.59                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.59                                         ( ( G ) = ( H ) ) ) =>
% 0.38/0.59                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.38/0.59                                         ( r1_tmap_1 @
% 0.38/0.59                                           C @ B @ 
% 0.38/0.59                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.38/0.59                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.38/0.59         X33 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X26)
% 0.38/0.59          | ~ (v2_pre_topc @ X26)
% 0.38/0.59          | ~ (l1_pre_topc @ X26)
% 0.38/0.59          | (v2_struct_0 @ X27)
% 0.38/0.59          | ~ (m1_pre_topc @ X27 @ X28)
% 0.38/0.59          | ~ (m1_pre_topc @ X29 @ X27)
% 0.38/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.59          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.38/0.59          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.38/0.59               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.38/0.59          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X33)
% 0.38/0.59          | ((X33) != (X31))
% 0.38/0.59          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X29))
% 0.38/0.59          | ~ (r2_hidden @ X33 @ X30)
% 0.38/0.59          | ~ (v3_pre_topc @ X30 @ X27)
% 0.38/0.59          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X27))
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.38/0.59          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.38/0.59          | ~ (v1_funct_1 @ X32)
% 0.38/0.59          | ~ (m1_pre_topc @ X29 @ X28)
% 0.38/0.59          | (v2_struct_0 @ X29)
% 0.38/0.59          | ~ (l1_pre_topc @ X28)
% 0.38/0.59          | ~ (v2_pre_topc @ X28)
% 0.38/0.59          | (v2_struct_0 @ X28))),
% 0.38/0.59      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X28)
% 0.38/0.59          | ~ (v2_pre_topc @ X28)
% 0.38/0.59          | ~ (l1_pre_topc @ X28)
% 0.38/0.59          | (v2_struct_0 @ X29)
% 0.38/0.59          | ~ (m1_pre_topc @ X29 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X32)
% 0.38/0.59          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.38/0.59          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 0.38/0.59          | ~ (v3_pre_topc @ X30 @ X27)
% 0.38/0.59          | ~ (r2_hidden @ X31 @ X30)
% 0.38/0.59          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X29))
% 0.38/0.59          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 0.38/0.59          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.38/0.59               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.38/0.59          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.38/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.59          | ~ (m1_pre_topc @ X29 @ X27)
% 0.38/0.59          | ~ (m1_pre_topc @ X27 @ X28)
% 0.38/0.59          | (v2_struct_0 @ X27)
% 0.38/0.59          | ~ (l1_pre_topc @ X26)
% 0.38/0.59          | ~ (v2_pre_topc @ X26)
% 0.38/0.59          | (v2_struct_0 @ X26))),
% 0.38/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_D)
% 0.38/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.59          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.59               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.38/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.38/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.38/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.38/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X1)
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | ~ (v2_pre_topc @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '15'])).
% 0.38/0.59  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_D)
% 0.38/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.38/0.59          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.38/0.59               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.38/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.38/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.38/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.38/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X1)
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | ~ (v2_pre_topc @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | (v2_struct_0 @ sk_C)
% 0.38/0.59          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.38/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.38/0.59          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.38/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.59          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.38/0.59          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.59          | (v2_struct_0 @ sk_D)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['12', '21'])).
% 0.38/0.59  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('26', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('27', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('28', plain, (((sk_F) = (sk_G))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.59  thf(t65_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( l1_pre_topc @ B ) =>
% 0.38/0.59           ( ( m1_pre_topc @ A @ B ) <=>
% 0.38/0.59             ( m1_pre_topc @
% 0.38/0.59               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X17)
% 0.38/0.59          | ~ (m1_pre_topc @ X18 @ X17)
% 0.38/0.59          | (m1_pre_topc @ X18 @ 
% 0.38/0.59             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.38/0.59          | ~ (l1_pre_topc @ X18))),
% 0.38/0.59      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | (m1_pre_topc @ X0 @ 
% 0.38/0.59             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.59          | ~ (l1_pre_topc @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_pre_topc @ X0 @ 
% 0.38/0.59           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.59          | ~ (l1_pre_topc @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.59  thf('35', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.38/0.59      inference('sup+', [status(thm)], ['30', '34'])).
% 0.38/0.59  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_m1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.59          | (l1_pre_topc @ X12)
% 0.38/0.59          | ~ (l1_pre_topc @ X13))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.59  thf('38', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('40', plain, ((l1_pre_topc @ sk_C)),
% 0.38/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['35', '40'])).
% 0.38/0.59  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | (v2_struct_0 @ sk_C)
% 0.38/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.38/0.59          | ~ (r2_hidden @ sk_F @ X0)
% 0.38/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.38/0.59          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.38/0.59          | (v2_struct_0 @ sk_D)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)],
% 0.38/0.59                ['22', '23', '24', '25', '26', '29', '41', '42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59        | ~ (r1_tarski @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.38/0.59        | ~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.38/0.59        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_C)
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['9', '43'])).
% 0.38/0.59  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.59          | (l1_pre_topc @ X12)
% 0.38/0.59          | ~ (l1_pre_topc @ X13))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.59  thf('47', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.59  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X10 : $i]:
% 0.38/0.59         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.38/0.59  thf(t59_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_pre_topc @
% 0.38/0.59             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.38/0.59           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X15 @ 
% 0.38/0.59             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.38/0.59          | (m1_pre_topc @ X15 @ X16)
% 0.38/0.59          | ~ (l1_pre_topc @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ 
% 0.38/0.59             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | (m1_pre_topc @ 
% 0.38/0.59             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_D)
% 0.38/0.59        | (m1_pre_topc @ 
% 0.38/0.59           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['51', '54'])).
% 0.38/0.59  thf('56', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('58', plain, ((l1_pre_topc @ sk_C)),
% 0.38/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.38/0.59      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X20 @ X21)
% 0.38/0.59          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.38/0.59          | ~ (l1_pre_topc @ X21))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_C)
% 0.38/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.59  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 0.38/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.38/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.59  thf(t3_subset, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (![X2 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.59  thf('65', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      (((r1_tarski @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.38/0.59        | ~ (l1_struct_0 @ sk_D))),
% 0.38/0.59      inference('sup+', [status(thm)], ['50', '65'])).
% 0.38/0.59  thf('67', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.59  thf('69', plain, ((l1_struct_0 @ sk_D)),
% 0.38/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.59  thf('70', plain, ((r1_tarski @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.38/0.59      inference('demod', [status(thm)], ['66', '69'])).
% 0.38/0.59  thf('71', plain,
% 0.38/0.59      (![X10 : $i]:
% 0.38/0.59         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.59  thf('72', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t2_subset, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r2_hidden @ X0 @ X1)
% 0.38/0.59          | (v1_xboole_0 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.38/0.59        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.38/0.59        | ~ (l1_struct_0 @ sk_D)
% 0.38/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['71', '74'])).
% 0.38/0.59  thf('76', plain, ((l1_struct_0 @ sk_D)),
% 0.38/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.38/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.38/0.59      inference('demod', [status(thm)], ['75', '76'])).
% 0.38/0.59  thf(fc2_struct_0, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.59       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      (![X14 : $i]:
% 0.38/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.38/0.59          | ~ (l1_struct_0 @ X14)
% 0.38/0.59          | (v2_struct_0 @ X14))),
% 0.38/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | ~ (l1_struct_0 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.59  thf('80', plain, ((l1_struct_0 @ sk_D)),
% 0.38/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.59  thf('81', plain,
% 0.38/0.59      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D)) | (v2_struct_0 @ sk_D))),
% 0.38/0.59      inference('demod', [status(thm)], ['79', '80'])).
% 0.38/0.59  thf('82', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('83', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))),
% 0.38/0.59      inference('clc', [status(thm)], ['81', '82'])).
% 0.38/0.59  thf('84', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_C)
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['44', '49', '70', '83'])).
% 0.38/0.59  thf('85', plain,
% 0.38/0.59      ((~ (v2_pre_topc @ sk_D)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_C)
% 0.38/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '84'])).
% 0.38/0.59  thf('86', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.59  thf('87', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X8 @ X9)
% 0.38/0.59          | (v2_pre_topc @ X8)
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.59  thf('88', plain,
% 0.38/0.59      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.59  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('91', plain, ((v2_pre_topc @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.38/0.59  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('93', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_C)
% 0.38/0.59        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['85', '91', '92'])).
% 0.38/0.59  thf('94', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('95', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_D)
% 0.38/0.59        | (v2_struct_0 @ sk_C)
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.38/0.59  thf('96', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('97', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.59  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('99', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.38/0.59      inference('clc', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('101', plain, ((v2_struct_0 @ sk_C)),
% 0.38/0.59      inference('clc', [status(thm)], ['99', '100'])).
% 0.38/0.59  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
