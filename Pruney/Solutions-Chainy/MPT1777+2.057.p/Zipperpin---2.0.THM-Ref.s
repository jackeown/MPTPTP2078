%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d9bDbnpAUP

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  246 (9563 expanded)
%              Number of leaves         :   46 (2694 expanded)
%              Depth                    :   33
%              Number of atoms          : 2124 (334100 expanded)
%              Number of equality atoms :   73 (9764 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X32 )
      | ( X32 != X30 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_hidden @ X32 @ X29 )
      | ~ ( v3_pre_topc @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v3_pre_topc @ X29 @ X26 )
      | ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_pre_topc @ X20 @ ( k1_tsep_1 @ X21 @ X20 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k1_tsep_1 @ X24 @ X23 @ X23 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k1_tsep_1 @ X24 @ X23 @ X23 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','49','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( X18
       != ( k1_tsep_1 @ X17 @ X16 @ X19 ) )
      | ( ( u1_struct_0 @ X18 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X19 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X19 ) @ X17 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X17 @ X16 @ X19 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_D @ sk_C @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_D @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_D @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_pre_topc @ X20 @ ( k1_tsep_1 @ X21 @ X20 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( ( u1_struct_0 @ X18 )
       != ( k2_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X19 ) ) )
      | ( X18
        = ( k1_tsep_1 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X1 )
       != ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( X1
        = ( k1_tsep_1 @ X2 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X1
        = ( k1_tsep_1 @ X2 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( ( u1_struct_0 @ X1 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( X1
        = ( k1_tsep_1 @ X0 @ X1 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(eq_res,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_pre_topc @ X1 )
      | ( X1
        = ( k1_tsep_1 @ X0 @ X1 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( sk_D
      = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('87',plain,(
    ! [X14: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('88',plain,
    ( ( v1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('91',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['88','94','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( sk_D
      = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['84','85','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( sk_D
      = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_D
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_D ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['76','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['29','40'])).

thf('108',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('109',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('110',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['88','94','99'])).

thf('111',plain,
    ( ( k1_tsep_1 @ sk_D @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['58','59'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['29','40'])).

thf('114',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','106','107','108','109','110','111','112','113','114'])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('123',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('125',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('126',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['97','98'])).

thf('133',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['128','135'])).

thf('137',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['128','135'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['143','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('149',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('151',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('152',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('154',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('155',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['29','40'])).

thf('156',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','149','152','153','154','155','156'])).

thf('158',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('160',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('161',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('162',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['160','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('166',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('168',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('169',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('171',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('172',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['170','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('176',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('177',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('178',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['132','133'])).

thf('180',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['131','134'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('184',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('185',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('187',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('188',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','169','182','188'])).

thf('190',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    $false ),
    inference(demod,[status(thm)],['0','197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d9bDbnpAUP
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 282 iterations in 0.192s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.65  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.65  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(t88_tmap_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65             ( l1_pre_topc @ B ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ![E:$i]:
% 0.47/0.65                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                         ( v1_funct_2 @
% 0.47/0.65                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                         ( m1_subset_1 @
% 0.47/0.65                           E @ 
% 0.47/0.65                           ( k1_zfmisc_1 @
% 0.47/0.65                             ( k2_zfmisc_1 @
% 0.47/0.65                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                       ( ( ( g1_pre_topc @
% 0.47/0.65                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.65                           ( D ) ) =>
% 0.47/0.65                         ( ![F:$i]:
% 0.47/0.65                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                             ( ![G:$i]:
% 0.47/0.65                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                 ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.65                                     ( r1_tmap_1 @
% 0.47/0.65                                       C @ B @ 
% 0.47/0.65                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.65                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65            ( l1_pre_topc @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65                ( l1_pre_topc @ B ) ) =>
% 0.47/0.65              ( ![C:$i]:
% 0.47/0.65                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65                  ( ![D:$i]:
% 0.47/0.65                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                      ( ![E:$i]:
% 0.47/0.65                        ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                            ( v1_funct_2 @
% 0.47/0.65                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                            ( m1_subset_1 @
% 0.47/0.65                              E @ 
% 0.47/0.65                              ( k1_zfmisc_1 @
% 0.47/0.65                                ( k2_zfmisc_1 @
% 0.47/0.65                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                          ( ( ( g1_pre_topc @
% 0.47/0.65                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.65                              ( D ) ) =>
% 0.47/0.65                            ( ![F:$i]:
% 0.47/0.65                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                                ( ![G:$i]:
% 0.47/0.65                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                    ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.65                                        ( r1_tmap_1 @
% 0.47/0.65                                          C @ B @ 
% 0.47/0.65                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.65                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.47/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d3_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf(dt_k2_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) =>
% 0.47/0.65       ( m1_subset_1 @
% 0.47/0.65         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X9 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.47/0.65          | ~ (l1_struct_0 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_struct_0 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X0)
% 0.47/0.65          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.47/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.65        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('6', plain, (((sk_F) = (sk_G))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.65        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.47/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_E @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t84_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.65             ( l1_pre_topc @ B ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ![E:$i]:
% 0.47/0.65                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65                         ( v1_funct_2 @
% 0.47/0.65                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                         ( m1_subset_1 @
% 0.47/0.65                           E @ 
% 0.47/0.65                           ( k1_zfmisc_1 @
% 0.47/0.65                             ( k2_zfmisc_1 @
% 0.47/0.65                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                       ( ( m1_pre_topc @ C @ D ) =>
% 0.47/0.65                         ( ![F:$i]:
% 0.47/0.65                           ( ( m1_subset_1 @
% 0.47/0.65                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.47/0.65                             ( ![G:$i]:
% 0.47/0.65                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.65                                 ( ![H:$i]:
% 0.47/0.65                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.65                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.47/0.65                                         ( r2_hidden @ G @ F ) & 
% 0.47/0.65                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.47/0.65                                         ( ( G ) = ( H ) ) ) =>
% 0.47/0.65                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.47/0.65                                         ( r1_tmap_1 @
% 0.47/0.65                                           C @ B @ 
% 0.47/0.65                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.47/0.65                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 0.47/0.65         X32 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X25)
% 0.47/0.65          | ~ (v2_pre_topc @ X25)
% 0.47/0.65          | ~ (l1_pre_topc @ X25)
% 0.47/0.65          | (v2_struct_0 @ X26)
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X27)
% 0.47/0.65          | ~ (m1_pre_topc @ X28 @ X26)
% 0.47/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.65          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.47/0.65          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.47/0.65               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.47/0.65          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X32)
% 0.47/0.65          | ((X32) != (X30))
% 0.47/0.65          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.47/0.65          | ~ (r2_hidden @ X32 @ X29)
% 0.47/0.65          | ~ (v3_pre_topc @ X29 @ X26)
% 0.47/0.65          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (m1_subset_1 @ X31 @ 
% 0.47/0.65               (k1_zfmisc_1 @ 
% 0.47/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.47/0.65          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.47/0.65          | ~ (v1_funct_1 @ X31)
% 0.47/0.65          | ~ (m1_pre_topc @ X28 @ X27)
% 0.47/0.65          | (v2_struct_0 @ X28)
% 0.47/0.65          | ~ (l1_pre_topc @ X27)
% 0.47/0.65          | ~ (v2_pre_topc @ X27)
% 0.47/0.65          | (v2_struct_0 @ X27))),
% 0.47/0.65      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X27)
% 0.47/0.65          | ~ (v2_pre_topc @ X27)
% 0.47/0.65          | ~ (l1_pre_topc @ X27)
% 0.47/0.65          | (v2_struct_0 @ X28)
% 0.47/0.65          | ~ (m1_pre_topc @ X28 @ X27)
% 0.47/0.65          | ~ (v1_funct_1 @ X31)
% 0.47/0.65          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.47/0.65          | ~ (m1_subset_1 @ X31 @ 
% 0.47/0.65               (k1_zfmisc_1 @ 
% 0.47/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.47/0.65          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (v3_pre_topc @ X29 @ X26)
% 0.47/0.65          | ~ (r2_hidden @ X30 @ X29)
% 0.47/0.65          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 0.47/0.65          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.47/0.65          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.47/0.65               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.47/0.65          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.47/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.65          | ~ (m1_pre_topc @ X28 @ X26)
% 0.47/0.65          | ~ (m1_pre_topc @ X26 @ X27)
% 0.47/0.65          | (v2_struct_0 @ X26)
% 0.47/0.65          | ~ (l1_pre_topc @ X25)
% 0.47/0.65          | ~ (v2_pre_topc @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_B)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.65          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.65               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.47/0.65          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.65          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.47/0.65          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.47/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['8', '10'])).
% 0.47/0.65  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_B)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.65               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.47/0.65          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.65          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.47/0.65  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t22_tsep_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X20)
% 0.47/0.65          | ~ (m1_pre_topc @ X20 @ X21)
% 0.47/0.65          | (m1_pre_topc @ X20 @ (k1_tsep_1 @ X21 @ X20 @ X22))
% 0.47/0.65          | ~ (m1_pre_topc @ X22 @ X21)
% 0.47/0.65          | (v2_struct_0 @ X22)
% 0.47/0.65          | ~ (l1_pre_topc @ X21)
% 0.47/0.65          | ~ (v2_pre_topc @ X21)
% 0.47/0.65          | (v2_struct_0 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.47/0.65          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.47/0.65          | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.47/0.65          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.47/0.65          | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C)
% 0.47/0.65        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.65  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C)
% 0.47/0.65        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 0.47/0.65      inference('clc', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('28', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('29', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t25_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.65           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.47/0.65             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X23)
% 0.47/0.65          | ~ (m1_pre_topc @ X23 @ X24)
% 0.47/0.65          | ((k1_tsep_1 @ X24 @ X23 @ X23)
% 0.47/0.65              = (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.47/0.65          | ~ (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (v2_pre_topc @ X24)
% 0.47/0.65          | (v2_struct_0 @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.47/0.65            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.47/0.65  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C) | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D)))),
% 0.47/0.65      inference('clc', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('39', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('40', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '40'])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X23)
% 0.47/0.65          | ~ (m1_pre_topc @ X23 @ X24)
% 0.47/0.65          | ((k1_tsep_1 @ X24 @ X23 @ X23)
% 0.47/0.65              = (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.47/0.65          | ~ (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (v2_pre_topc @ X24)
% 0.47/0.65          | (v2_struct_0 @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_D)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_D)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.65        | ((k1_tsep_1 @ sk_D @ sk_C @ sk_C)
% 0.47/0.65            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X6 @ X7)
% 0.47/0.65          | (v2_pre_topc @ X6)
% 0.47/0.65          | ~ (l1_pre_topc @ X7)
% 0.47/0.65          | ~ (v2_pre_topc @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.65  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('49', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.47/0.65  thf('50', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_m1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X11 @ X12)
% 0.47/0.65          | (l1_pre_topc @ X11)
% 0.47/0.65          | ~ (l1_pre_topc @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('52', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.65  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_D)
% 0.47/0.65        | ((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D))
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['43', '49', '54', '55'])).
% 0.47/0.65  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C) | ((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D)))),
% 0.47/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.47/0.65  thf('59', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('60', plain, (((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf(d2_tsep_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.47/0.65                     ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.47/0.65                     ( ( u1_struct_0 @ D ) =
% 0.47/0.65                       ( k2_xboole_0 @
% 0.47/0.65                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X16)
% 0.47/0.65          | ~ (m1_pre_topc @ X16 @ X17)
% 0.47/0.65          | (v2_struct_0 @ X18)
% 0.47/0.65          | ~ (v1_pre_topc @ X18)
% 0.47/0.65          | ~ (m1_pre_topc @ X18 @ X17)
% 0.47/0.65          | ((X18) != (k1_tsep_1 @ X17 @ X16 @ X19))
% 0.47/0.65          | ((u1_struct_0 @ X18)
% 0.47/0.65              = (k2_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X19)))
% 0.47/0.65          | ~ (m1_pre_topc @ X19 @ X17)
% 0.47/0.65          | (v2_struct_0 @ X19)
% 0.47/0.65          | ~ (l1_pre_topc @ X17)
% 0.47/0.65          | (v2_struct_0 @ X17))),
% 0.47/0.65      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X17)
% 0.47/0.65          | ~ (l1_pre_topc @ X17)
% 0.47/0.65          | (v2_struct_0 @ X19)
% 0.47/0.65          | ~ (m1_pre_topc @ X19 @ X17)
% 0.47/0.65          | ((u1_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X19))
% 0.47/0.65              = (k2_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X19)))
% 0.47/0.65          | ~ (m1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X19) @ X17)
% 0.47/0.65          | ~ (v1_pre_topc @ (k1_tsep_1 @ X17 @ X16 @ X19))
% 0.47/0.65          | (v2_struct_0 @ (k1_tsep_1 @ X17 @ X16 @ X19))
% 0.47/0.65          | ~ (m1_pre_topc @ X16 @ X17)
% 0.47/0.65          | (v2_struct_0 @ X16))),
% 0.47/0.65      inference('simplify', [status(thm)], ['61'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      ((~ (m1_pre_topc @ sk_D @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ (k1_tsep_1 @ sk_D @ sk_C @ sk_C))
% 0.47/0.65        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_D @ sk_C @ sk_C))
% 0.47/0.65        | ((u1_struct_0 @ (k1_tsep_1 @ sk_D @ sk_C @ sk_C))
% 0.47/0.65            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 0.47/0.65        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['60', '62'])).
% 0.47/0.65  thf('64', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X20)
% 0.47/0.65          | ~ (m1_pre_topc @ X20 @ X21)
% 0.47/0.65          | (m1_pre_topc @ X20 @ (k1_tsep_1 @ X21 @ X20 @ X22))
% 0.47/0.65          | ~ (m1_pre_topc @ X22 @ X21)
% 0.47/0.65          | (v2_struct_0 @ X22)
% 0.47/0.65          | ~ (l1_pre_topc @ X21)
% 0.47/0.65          | ~ (v2_pre_topc @ X21)
% 0.47/0.65          | (v2_struct_0 @ X21))),
% 0.47/0.65      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.47/0.65          | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.47/0.65          | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.47/0.65          | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ X0))
% 0.47/0.65          | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_D)
% 0.47/0.65        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['64', '70'])).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.47/0.65        | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('simplify', [status(thm)], ['71'])).
% 0.47/0.65  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('74', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_D)
% 0.47/0.65        | (m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 0.47/0.65      inference('clc', [status(thm)], ['72', '73'])).
% 0.47/0.65  thf('75', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('76', plain, ((m1_pre_topc @ sk_D @ (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['74', '75'])).
% 0.47/0.65  thf('77', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(idempotence_k2_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.65  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X16)
% 0.47/0.65          | ~ (m1_pre_topc @ X16 @ X17)
% 0.47/0.65          | (v2_struct_0 @ X18)
% 0.47/0.65          | ~ (v1_pre_topc @ X18)
% 0.47/0.65          | ~ (m1_pre_topc @ X18 @ X17)
% 0.47/0.65          | ((u1_struct_0 @ X18)
% 0.47/0.65              != (k2_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X19)))
% 0.47/0.65          | ((X18) = (k1_tsep_1 @ X17 @ X16 @ X19))
% 0.47/0.65          | ~ (m1_pre_topc @ X19 @ X17)
% 0.47/0.65          | (v2_struct_0 @ X19)
% 0.47/0.65          | ~ (l1_pre_topc @ X17)
% 0.47/0.65          | (v2_struct_0 @ X17))),
% 0.47/0.65      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((u1_struct_0 @ X1) != (u1_struct_0 @ X0))
% 0.47/0.65          | (v2_struct_0 @ X2)
% 0.47/0.65          | ~ (l1_pre_topc @ X2)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.65          | ((X1) = (k1_tsep_1 @ X2 @ X0 @ X0))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X2)
% 0.47/0.65          | ~ (v1_pre_topc @ X1)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X1)
% 0.47/0.65          | ~ (v1_pre_topc @ X1)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X2)
% 0.47/0.65          | ((X1) = (k1_tsep_1 @ X2 @ X0 @ X0))
% 0.47/0.65          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X2)
% 0.47/0.65          | (v2_struct_0 @ X2)
% 0.47/0.65          | ((u1_struct_0 @ X1) != (u1_struct_0 @ X0)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['80'])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | ((X1) = (k1_tsep_1 @ X0 @ X1 @ X1))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | ~ (v1_pre_topc @ X1)
% 0.47/0.65          | (v2_struct_0 @ X1))),
% 0.47/0.65      inference('eq_res', [status(thm)], ['81'])).
% 0.47/0.65  thf('83', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (v1_pre_topc @ X1)
% 0.47/0.65          | ((X1) = (k1_tsep_1 @ X0 @ X1 @ X1))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['82'])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | ((sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.47/0.65        | ~ (v1_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup-', [status(thm)], ['77', '83'])).
% 0.47/0.65  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(fc6_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ( v1_pre_topc @
% 0.47/0.65           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.65         ( v2_pre_topc @
% 0.47/0.65           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (![X14 : $i]:
% 0.47/0.65         ((v1_pre_topc @ 
% 0.47/0.65           (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 0.47/0.65          | ~ (l1_pre_topc @ X14)
% 0.47/0.65          | ~ (v2_pre_topc @ X14))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      (((v1_pre_topc @ sk_D) | ~ (v2_pre_topc @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['86', '87'])).
% 0.47/0.65  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X6 @ X7)
% 0.47/0.65          | (v2_pre_topc @ X6)
% 0.47/0.65          | ~ (l1_pre_topc @ X7)
% 0.47/0.65          | ~ (v2_pre_topc @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.65  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('94', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.47/0.65  thf('95', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('96', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X11 @ X12)
% 0.47/0.65          | (l1_pre_topc @ X11)
% 0.47/0.65          | ~ (l1_pre_topc @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('97', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.65  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('99', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['97', '98'])).
% 0.47/0.65  thf('100', plain, ((v1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['88', '94', '99'])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | ((sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D)))),
% 0.47/0.65      inference('demod', [status(thm)], ['84', '85', '100'])).
% 0.47/0.65  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('103', plain,
% 0.47/0.65      ((((sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D)) | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['101', '102'])).
% 0.47/0.65  thf('104', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('105', plain, (((sk_D) = (k1_tsep_1 @ sk_A @ sk_D @ sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['103', '104'])).
% 0.47/0.65  thf('106', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['76', '105'])).
% 0.47/0.65  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '40'])).
% 0.47/0.65  thf('108', plain, (((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('109', plain, (((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('110', plain, ((v1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['88', '94', '99'])).
% 0.47/0.65  thf('111', plain, (((k1_tsep_1 @ sk_D @ sk_C @ sk_C) = (sk_D))),
% 0.47/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.47/0.65  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '40'])).
% 0.47/0.65  thf('114', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('115', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_D))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['63', '106', '107', '108', '109', '110', '111', '112', '113', 
% 0.47/0.65                 '114'])).
% 0.47/0.65  thf('116', plain,
% 0.47/0.65      ((((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('simplify', [status(thm)], ['115'])).
% 0.47/0.65  thf('117', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('118', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_C) | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.47/0.65      inference('clc', [status(thm)], ['116', '117'])).
% 0.47/0.65  thf('119', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('120', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['118', '119'])).
% 0.47/0.65  thf('121', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('122', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['118', '119'])).
% 0.47/0.65  thf('123', plain,
% 0.47/0.65      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 0.47/0.65      inference('sup+', [status(thm)], ['121', '122'])).
% 0.47/0.65  thf('124', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf(dt_l1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.65  thf('125', plain,
% 0.47/0.65      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('126', plain, ((l1_struct_0 @ sk_D)),
% 0.47/0.65      inference('sup-', [status(thm)], ['124', '125'])).
% 0.47/0.65  thf('127', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['123', '126'])).
% 0.47/0.65  thf('128', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_D))),
% 0.47/0.65      inference('demod', [status(thm)], ['120', '127'])).
% 0.47/0.65  thf('129', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('130', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['123', '126'])).
% 0.47/0.65  thf('131', plain,
% 0.47/0.65      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['129', '130'])).
% 0.47/0.65  thf('132', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.65      inference('demod', [status(thm)], ['97', '98'])).
% 0.47/0.65  thf('133', plain,
% 0.47/0.65      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('134', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.65  thf('135', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['131', '134'])).
% 0.47/0.65  thf('136', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['128', '135'])).
% 0.47/0.65  thf('137', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['128', '135'])).
% 0.47/0.65  thf('138', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_B)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.65               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.47/0.65          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.65          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.47/0.65          | ~ (m1_subset_1 @ X3 @ (k2_struct_0 @ sk_C))
% 0.47/0.65          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.65          | (v2_struct_0 @ X1)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['16', '136', '137'])).
% 0.47/0.65  thf('139', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ sk_C)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.65          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.65          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.47/0.65          | ~ (r2_hidden @ sk_F @ X0)
% 0.47/0.65          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.47/0.65          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.65          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['7', '138'])).
% 0.47/0.65  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('142', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('143', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('144', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('145', plain, (((sk_F) = (sk_G))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('146', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['144', '145'])).
% 0.47/0.65  thf('147', plain,
% 0.47/0.65      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['143', '146'])).
% 0.47/0.65  thf('148', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.65  thf('149', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['147', '148'])).
% 0.47/0.65  thf('150', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['123', '126'])).
% 0.47/0.65  thf('151', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['131', '134'])).
% 0.47/0.65  thf('152', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['150', '151'])).
% 0.47/0.65  thf('153', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['150', '151'])).
% 0.47/0.65  thf('154', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['147', '148'])).
% 0.47/0.65  thf('155', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '40'])).
% 0.47/0.65  thf('156', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('157', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ sk_C)
% 0.47/0.65          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.47/0.65          | ~ (r2_hidden @ sk_F @ X0)
% 0.47/0.65          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.65          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.47/0.65          | (v2_struct_0 @ sk_D)
% 0.47/0.65          | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['139', '140', '141', '142', '149', '152', '153', '154', 
% 0.47/0.65                 '155', '156'])).
% 0.47/0.65  thf('158', plain,
% 0.47/0.65      ((~ (l1_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_B)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 0.47/0.65        | ~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.65        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '157'])).
% 0.47/0.65  thf('159', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.65  thf('160', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['118', '119'])).
% 0.47/0.65  thf('161', plain,
% 0.47/0.65      (![X9 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.47/0.65          | ~ (l1_struct_0 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.65  thf(t3_subset, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.65  thf('162', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i]:
% 0.47/0.65         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.65  thf('163', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X0)
% 0.47/0.65          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['161', '162'])).
% 0.47/0.65  thf('164', plain,
% 0.47/0.65      (((r1_tarski @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_D))),
% 0.47/0.65      inference('sup+', [status(thm)], ['160', '163'])).
% 0.47/0.65  thf('165', plain, ((l1_struct_0 @ sk_D)),
% 0.47/0.65      inference('sup-', [status(thm)], ['124', '125'])).
% 0.47/0.65  thf('166', plain,
% 0.47/0.65      ((r1_tarski @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['164', '165'])).
% 0.47/0.65  thf('167', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['131', '134'])).
% 0.47/0.65  thf('168', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['150', '151'])).
% 0.47/0.65  thf('169', plain,
% 0.47/0.65      ((r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.47/0.65  thf('170', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('171', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['144', '145'])).
% 0.47/0.65  thf(t2_subset, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.65       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.65  thf('172', plain,
% 0.47/0.65      (![X1 : $i, X2 : $i]:
% 0.47/0.65         ((r2_hidden @ X1 @ X2)
% 0.47/0.65          | (v1_xboole_0 @ X2)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.65  thf('173', plain,
% 0.47/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.47/0.65        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['171', '172'])).
% 0.47/0.65  thf('174', plain,
% 0.47/0.65      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_C)
% 0.47/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['170', '173'])).
% 0.47/0.65  thf('175', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.65  thf('176', plain,
% 0.47/0.65      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.47/0.65      inference('demod', [status(thm)], ['174', '175'])).
% 0.47/0.65  thf(fc2_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.65  thf('177', plain,
% 0.47/0.65      (![X13 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.47/0.65          | ~ (l1_struct_0 @ X13)
% 0.47/0.65          | (v2_struct_0 @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.65  thf('178', plain,
% 0.47/0.65      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['176', '177'])).
% 0.47/0.65  thf('179', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.65  thf('180', plain,
% 0.47/0.65      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['178', '179'])).
% 0.47/0.65  thf('181', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('182', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['180', '181'])).
% 0.47/0.65  thf('183', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['131', '134'])).
% 0.47/0.65  thf(fc10_tops_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.47/0.65  thf('184', plain,
% 0.47/0.65      (![X15 : $i]:
% 0.47/0.65         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.47/0.65          | ~ (l1_pre_topc @ X15)
% 0.47/0.65          | ~ (v2_pre_topc @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.65  thf('185', plain,
% 0.47/0.65      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_D)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_D))),
% 0.47/0.65      inference('sup+', [status(thm)], ['183', '184'])).
% 0.47/0.65  thf('186', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.47/0.65  thf('187', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('188', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.47/0.65      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.47/0.65  thf('189', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_B)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['158', '159', '169', '182', '188'])).
% 0.47/0.65  thf('190', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('191', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | (v2_struct_0 @ sk_C)
% 0.47/0.65        | (v2_struct_0 @ sk_D)
% 0.47/0.65        | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['189', '190'])).
% 0.47/0.65  thf('192', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('193', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['191', '192'])).
% 0.47/0.65  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('195', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.47/0.65      inference('clc', [status(thm)], ['193', '194'])).
% 0.47/0.65  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('197', plain, ((v2_struct_0 @ sk_C)),
% 0.47/0.65      inference('clc', [status(thm)], ['195', '196'])).
% 0.47/0.65  thf('198', plain, ($false), inference('demod', [status(thm)], ['0', '197'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
