%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qwk4nyLld8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:18 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 614 expanded)
%              Number of leaves         :   35 ( 187 expanded)
%              Depth                    :   24
%              Number of atoms          : 2345 (23700 expanded)
%              Number of equality atoms :   14 ( 272 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t85_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ B )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                     => ( ( ( v3_pre_topc @ F @ B )
                                          & ( r2_hidden @ G @ F )
                                          & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                          & ( G = H ) )
                                       => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                        <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_tmap_1])).

thf('0',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X30 )
      | ( X30 != X33 )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['13'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['11'])).

thf('55',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('76',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['64','65'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

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

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('84',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v3_pre_topc @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D_1 )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['73','79','80','90'])).

thf('92',plain,
    ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['70','91'])).

thf('93',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F ),
    inference(clc,[status(thm)],['96','97'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_tmap_1,axiom,(
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
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X41 )
      | ( X41 != X39 )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X41 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('107',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X39 )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ~ ( l1_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
        | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('119',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
        | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
      | ~ ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['103','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('126',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( m1_connsp_2 @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 @ X22 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('129',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['64','65'])).

thf('130',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['124','131'])).

thf('133',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['93','94'])).

thf('134',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('139',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['123','136','139'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['8','17','18','53','54','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qwk4nyLld8
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 358 iterations in 0.174s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.63  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.45/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.63  thf(sk_H_type, type, sk_H: $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(t85_tmap_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.63             ( l1_pre_topc @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.45/0.63               ( ![D:$i]:
% 0.45/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.45/0.63                   ( ![E:$i]:
% 0.45/0.63                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.63                         ( v1_funct_2 @
% 0.45/0.63                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.63                         ( m1_subset_1 @
% 0.45/0.63                           E @ 
% 0.45/0.63                           ( k1_zfmisc_1 @
% 0.45/0.63                             ( k2_zfmisc_1 @
% 0.45/0.63                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.45/0.63                       ( ( m1_pre_topc @ C @ D ) =>
% 0.45/0.63                         ( ![F:$i]:
% 0.45/0.63                           ( ( m1_subset_1 @
% 0.45/0.63                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.63                             ( ![G:$i]:
% 0.45/0.63                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.63                                 ( ![H:$i]:
% 0.45/0.63                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.63                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.45/0.63                                         ( r2_hidden @ G @ F ) & 
% 0.45/0.63                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.45/0.63                                         ( ( G ) = ( H ) ) ) =>
% 0.45/0.63                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.45/0.63                                         ( r1_tmap_1 @
% 0.45/0.63                                           C @ A @ 
% 0.45/0.63                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.45/0.63                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.63            ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.63                ( l1_pre_topc @ B ) ) =>
% 0.45/0.63              ( ![C:$i]:
% 0.45/0.63                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.45/0.63                  ( ![D:$i]:
% 0.45/0.63                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.45/0.63                      ( ![E:$i]:
% 0.45/0.63                        ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.63                            ( v1_funct_2 @
% 0.45/0.63                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.63                            ( m1_subset_1 @
% 0.45/0.63                              E @ 
% 0.45/0.63                              ( k1_zfmisc_1 @
% 0.45/0.63                                ( k2_zfmisc_1 @
% 0.45/0.63                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.45/0.63                          ( ( m1_pre_topc @ C @ D ) =>
% 0.45/0.63                            ( ![F:$i]:
% 0.45/0.63                              ( ( m1_subset_1 @
% 0.45/0.63                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.63                                ( ![G:$i]:
% 0.45/0.63                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.63                                    ( ![H:$i]:
% 0.45/0.63                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.63                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.45/0.63                                            ( r2_hidden @ G @ F ) & 
% 0.45/0.63                                            ( r1_tarski @
% 0.45/0.63                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.45/0.63                                            ( ( G ) = ( H ) ) ) =>
% 0.45/0.63                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.45/0.63                                            ( r1_tmap_1 @
% 0.45/0.63                                              C @ A @ 
% 0.45/0.63                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.45/0.63                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('5', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.63         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) | 
% 0.45/0.63       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('10', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.45/0.63      inference('split', [status(esa)], ['11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.45/0.63         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('split', [status(esa)], ['13'])).
% 0.45/0.63  thf('15', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.63         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)) | 
% 0.45/0.63       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (~
% 0.45/0.63       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.45/0.63       ~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.45/0.63      inference('split', [status(esa)], ['6'])).
% 0.45/0.63  thf('19', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_E @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t81_tmap_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.63             ( l1_pre_topc @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ![D:$i]:
% 0.45/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.63                   ( ![E:$i]:
% 0.45/0.63                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.63                         ( v1_funct_2 @
% 0.45/0.63                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.63                         ( m1_subset_1 @
% 0.45/0.63                           E @ 
% 0.45/0.63                           ( k1_zfmisc_1 @
% 0.45/0.63                             ( k2_zfmisc_1 @
% 0.45/0.63                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.63                       ( ![F:$i]:
% 0.45/0.63                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.63                           ( ![G:$i]:
% 0.45/0.63                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.63                               ( ( ( ( F ) = ( G ) ) & 
% 0.45/0.63                                   ( m1_pre_topc @ D @ C ) & 
% 0.45/0.63                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.45/0.63                                 ( r1_tmap_1 @
% 0.45/0.63                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.45/0.63                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X27)
% 0.45/0.63          | ~ (v2_pre_topc @ X27)
% 0.45/0.63          | ~ (l1_pre_topc @ X27)
% 0.45/0.63          | (v2_struct_0 @ X28)
% 0.45/0.63          | ~ (m1_pre_topc @ X28 @ X29)
% 0.45/0.63          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.45/0.63          | ~ (m1_pre_topc @ X28 @ X31)
% 0.45/0.63          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X30)
% 0.45/0.63          | ((X30) != (X33))
% 0.45/0.63          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.45/0.63             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.45/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.45/0.63          | ~ (m1_subset_1 @ X32 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.45/0.63          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.45/0.63          | ~ (v1_funct_1 @ X32)
% 0.45/0.63          | ~ (m1_pre_topc @ X31 @ X29)
% 0.45/0.63          | (v2_struct_0 @ X31)
% 0.45/0.63          | ~ (l1_pre_topc @ X29)
% 0.45/0.63          | ~ (v2_pre_topc @ X29)
% 0.45/0.63          | (v2_struct_0 @ X29))),
% 0.45/0.63      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X29)
% 0.45/0.63          | ~ (v2_pre_topc @ X29)
% 0.45/0.63          | ~ (l1_pre_topc @ X29)
% 0.45/0.63          | (v2_struct_0 @ X31)
% 0.45/0.63          | ~ (m1_pre_topc @ X31 @ X29)
% 0.45/0.63          | ~ (v1_funct_1 @ X32)
% 0.45/0.63          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.45/0.63          | ~ (m1_subset_1 @ X32 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.45/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.45/0.63          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.45/0.63             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.45/0.63          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X33)
% 0.45/0.63          | ~ (m1_pre_topc @ X28 @ X31)
% 0.45/0.63          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.45/0.63          | ~ (m1_pre_topc @ X28 @ X29)
% 0.45/0.63          | (v2_struct_0 @ X28)
% 0.45/0.63          | ~ (l1_pre_topc @ X27)
% 0.45/0.63          | ~ (v2_pre_topc @ X27)
% 0.45/0.63          | (v2_struct_0 @ X27))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.45/0.63          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2)
% 0.45/0.63          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.45/0.63             (k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.45/0.63          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.45/0.63               (u1_struct_0 @ sk_A))
% 0.45/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.63          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.45/0.63          | (v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (l1_pre_topc @ X1)
% 0.45/0.63          | ~ (v2_pre_topc @ X1)
% 0.45/0.63          | (v2_struct_0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '24'])).
% 0.45/0.63  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.45/0.63          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2)
% 0.45/0.63          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.45/0.63             (k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.45/0.63          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.45/0.63          | (v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (l1_pre_topc @ X1)
% 0.45/0.63          | ~ (v2_pre_topc @ X1)
% 0.45/0.63          | (v2_struct_0 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((![X0 : $i, X1 : $i]:
% 0.45/0.63          ((v2_struct_0 @ X0)
% 0.45/0.63           | ~ (v2_pre_topc @ X0)
% 0.45/0.63           | ~ (l1_pre_topc @ X0)
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.45/0.63           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.45/0.63              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.45/0.63           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.45/0.63           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63           | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.63           | (v2_struct_0 @ X1)
% 0.45/0.63           | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '30'])).
% 0.45/0.63  thf('32', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('33', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('34', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      ((![X0 : $i, X1 : $i]:
% 0.45/0.63          ((v2_struct_0 @ X0)
% 0.45/0.63           | ~ (v2_pre_topc @ X0)
% 0.45/0.63           | ~ (l1_pre_topc @ X0)
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.45/0.63           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.45/0.63              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.45/0.63           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.45/0.63           | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.63           | (v2_struct_0 @ X1)
% 0.45/0.63           | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['31', '34'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          ((v2_struct_0 @ sk_A)
% 0.45/0.63           | (v2_struct_0 @ sk_C_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.45/0.63           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | ~ (l1_pre_topc @ X0)
% 0.45/0.63           | ~ (v2_pre_topc @ X0)
% 0.45/0.63           | (v2_struct_0 @ X0)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '35'])).
% 0.45/0.63  thf('37', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          ((v2_struct_0 @ sk_A)
% 0.45/0.63           | (v2_struct_0 @ sk_C_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.45/0.63           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | ~ (l1_pre_topc @ X0)
% 0.45/0.63           | ~ (v2_pre_topc @ X0)
% 0.45/0.63           | (v2_struct_0 @ X0)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_B)
% 0.45/0.63         | ~ (v2_pre_topc @ sk_B)
% 0.45/0.63         | ~ (l1_pre_topc @ sk_B)
% 0.45/0.63         | (v2_struct_0 @ sk_D_1)
% 0.45/0.63         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.45/0.63         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63            (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63         | (v2_struct_0 @ sk_C_1)
% 0.45/0.63         | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '38'])).
% 0.45/0.63  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('42', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_B)
% 0.45/0.63         | (v2_struct_0 @ sk_D_1)
% 0.45/0.63         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63            (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.45/0.63         | (v2_struct_0 @ sk_C_1)
% 0.45/0.63         | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.63      inference('split', [status(esa)], ['13'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_A)
% 0.45/0.63         | (v2_struct_0 @ sk_C_1)
% 0.45/0.63         | (v2_struct_0 @ sk_D_1)
% 0.45/0.63         | (v2_struct_0 @ sk_B)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.45/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C_1)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.45/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.63  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D_1)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.45/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('clc', [status(thm)], ['47', '48'])).
% 0.45/0.63  thf('50', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_D_1))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.45/0.63             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.63      inference('clc', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf('52', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) | 
% 0.45/0.63       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))),
% 0.45/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.45/0.63       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.45/0.63      inference('split', [status(esa)], ['11'])).
% 0.45/0.63  thf('55', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('56', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      (![X3 : $i, X5 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf(t39_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.63               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X13 @ X14)
% 0.45/0.63          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.63          | ~ (l1_pre_topc @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X0)
% 0.45/0.63          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.63          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.45/0.63        | ~ (l1_pre_topc @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['55', '60'])).
% 0.45/0.63  thf('62', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_m1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X11 @ X12)
% 0.45/0.63          | (l1_pre_topc @ X11)
% 0.45/0.63          | ~ (l1_pre_topc @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.63  thf('64', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.63  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('66', plain, ((l1_pre_topc @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['61', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i]:
% 0.45/0.63         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('69', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf('70', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['61', '66'])).
% 0.45/0.63  thf(t9_connsp_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.63             ( ![C:$i]:
% 0.45/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.63                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.45/0.63                      ( ![D:$i]:
% 0.45/0.63                        ( ( m1_subset_1 @
% 0.45/0.63                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.45/0.63                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.63          | ~ (v3_pre_topc @ X20 @ X21)
% 0.45/0.63          | (r1_tarski @ (sk_D @ X22 @ X20 @ X21) @ X20)
% 0.45/0.63          | ~ (r2_hidden @ X22 @ X20)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | ~ (v2_pre_topc @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21))),
% 0.45/0.63      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (v2_pre_topc @ sk_D_1)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_D_1)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (r2_hidden @ X0 @ sk_F)
% 0.45/0.63          | (r1_tarski @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_F)
% 0.45/0.63          | ~ (v3_pre_topc @ sk_F @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.63  thf('74', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X9 @ X10)
% 0.45/0.63          | (v2_pre_topc @ X9)
% 0.45/0.63          | ~ (l1_pre_topc @ X10)
% 0.45/0.63          | ~ (v2_pre_topc @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      ((~ (v2_pre_topc @ sk_B)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_B)
% 0.45/0.63        | (v2_pre_topc @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.63  thf('77', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('79', plain, ((v2_pre_topc @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.45/0.63  thf('80', plain, ((l1_pre_topc @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['61', '66'])).
% 0.45/0.63  thf(t33_tops_2, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.63               ( ( v3_pre_topc @ B @ A ) =>
% 0.45/0.63                 ( ![D:$i]:
% 0.45/0.63                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.45/0.63                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.63          | ~ (v3_pre_topc @ X16 @ X17)
% 0.45/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.63          | (v3_pre_topc @ X18 @ X19)
% 0.45/0.63          | ((X18) != (X16))
% 0.45/0.63          | ~ (m1_pre_topc @ X19 @ X17)
% 0.45/0.63          | ~ (l1_pre_topc @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X17)
% 0.45/0.63          | ~ (m1_pre_topc @ X19 @ X17)
% 0.45/0.63          | (v3_pre_topc @ X16 @ X19)
% 0.45/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.63          | ~ (v3_pre_topc @ X16 @ X17)
% 0.45/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['83'])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.63          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.45/0.63          | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.45/0.63          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63          | ~ (l1_pre_topc @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['82', '84'])).
% 0.45/0.63  thf('86', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.45/0.63        | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.45/0.63        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['81', '85'])).
% 0.45/0.63  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('88', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('89', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('90', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (r2_hidden @ X0 @ sk_F)
% 0.45/0.63          | (r1_tarski @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_F))),
% 0.45/0.63      inference('demod', [status(thm)], ['73', '79', '80', '90'])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      (((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)
% 0.45/0.63        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.45/0.63        | (v2_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['70', '91'])).
% 0.45/0.63  thf('93', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('94', plain, (((sk_G) = (sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('95', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.45/0.63      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      (((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)
% 0.45/0.63        | (v2_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['92', '95'])).
% 0.45/0.63  thf('97', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('98', plain, ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)),
% 0.45/0.63      inference('clc', [status(thm)], ['96', '97'])).
% 0.45/0.63  thf(t1_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.63       ( r1_tarski @ A @ C ) ))).
% 0.45/0.63  thf('99', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2)
% 0.45/0.63          | (r1_tarski @ X0 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ X0)
% 0.45/0.63          | ~ (r1_tarski @ sk_F @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.63  thf('101', plain,
% 0.45/0.63      ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['69', '100'])).
% 0.45/0.63  thf('102', plain,
% 0.45/0.63      (![X3 : $i, X5 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('103', plain,
% 0.45/0.63      ((m1_subset_1 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['101', '102'])).
% 0.45/0.63  thf('104', plain,
% 0.45/0.63      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('105', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_E @ 
% 0.45/0.63        (k1_zfmisc_1 @ 
% 0.45/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t83_tmap_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.63             ( l1_pre_topc @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ![D:$i]:
% 0.45/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.63                   ( ![E:$i]:
% 0.45/0.63                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.63                         ( v1_funct_2 @
% 0.45/0.63                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.63                         ( m1_subset_1 @
% 0.45/0.63                           E @ 
% 0.45/0.63                           ( k1_zfmisc_1 @
% 0.45/0.63                             ( k2_zfmisc_1 @
% 0.45/0.63                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.63                       ( ( m1_pre_topc @ C @ D ) =>
% 0.45/0.63                         ( ![F:$i]:
% 0.45/0.63                           ( ( m1_subset_1 @
% 0.45/0.63                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.45/0.63                             ( ![G:$i]:
% 0.45/0.63                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.63                                 ( ![H:$i]:
% 0.45/0.63                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.63                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.45/0.63                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.45/0.63                                         ( ( G ) = ( H ) ) ) =>
% 0.45/0.63                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.45/0.63                                         ( r1_tmap_1 @
% 0.45/0.63                                           C @ B @ 
% 0.45/0.63                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.45/0.63                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('106', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 0.45/0.63         X41 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X34)
% 0.45/0.63          | ~ (v2_pre_topc @ X34)
% 0.45/0.63          | ~ (l1_pre_topc @ X34)
% 0.45/0.63          | (v2_struct_0 @ X35)
% 0.45/0.63          | ~ (m1_pre_topc @ X35 @ X36)
% 0.45/0.63          | ~ (m1_pre_topc @ X37 @ X35)
% 0.45/0.63          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.45/0.63          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.45/0.63          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.45/0.63               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.45/0.63          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X41)
% 0.45/0.63          | ((X41) != (X39))
% 0.45/0.63          | ~ (m1_connsp_2 @ X38 @ X35 @ X41)
% 0.45/0.63          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.45/0.63          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X35))
% 0.45/0.63          | ~ (m1_subset_1 @ X40 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.45/0.63          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.45/0.63          | ~ (v1_funct_1 @ X40)
% 0.45/0.63          | ~ (m1_pre_topc @ X37 @ X36)
% 0.45/0.63          | (v2_struct_0 @ X37)
% 0.45/0.63          | ~ (l1_pre_topc @ X36)
% 0.45/0.63          | ~ (v2_pre_topc @ X36)
% 0.45/0.63          | (v2_struct_0 @ X36))),
% 0.45/0.63      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.45/0.63  thf('107', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X36)
% 0.45/0.63          | ~ (v2_pre_topc @ X36)
% 0.45/0.63          | ~ (l1_pre_topc @ X36)
% 0.45/0.63          | (v2_struct_0 @ X37)
% 0.45/0.63          | ~ (m1_pre_topc @ X37 @ X36)
% 0.45/0.63          | ~ (v1_funct_1 @ X40)
% 0.45/0.63          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.45/0.63          | ~ (m1_subset_1 @ X40 @ 
% 0.45/0.63               (k1_zfmisc_1 @ 
% 0.45/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.45/0.63          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.45/0.63          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.45/0.63          | ~ (m1_connsp_2 @ X38 @ X35 @ X39)
% 0.45/0.63          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X39)
% 0.45/0.63          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.45/0.63               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.45/0.63          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.45/0.63          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.45/0.63          | ~ (m1_pre_topc @ X37 @ X35)
% 0.45/0.63          | ~ (m1_pre_topc @ X35 @ X36)
% 0.45/0.63          | (v2_struct_0 @ X35)
% 0.45/0.63          | ~ (l1_pre_topc @ X34)
% 0.45/0.63          | ~ (v2_pre_topc @ X34)
% 0.45/0.63          | (v2_struct_0 @ X34))),
% 0.45/0.63      inference('simplify', [status(thm)], ['106'])).
% 0.45/0.63  thf('108', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.45/0.63          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.45/0.63          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.45/0.63          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3)
% 0.45/0.63          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.45/0.63          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.63          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.45/0.63               (u1_struct_0 @ sk_A))
% 0.45/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.63          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.63          | (v2_struct_0 @ X1)
% 0.45/0.63          | ~ (l1_pre_topc @ X0)
% 0.45/0.63          | ~ (v2_pre_topc @ X0)
% 0.45/0.63          | (v2_struct_0 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['105', '107'])).
% 0.45/0.63  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('111', plain,
% 0.45/0.63      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('112', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('113', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_D_1)
% 0.45/0.63          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.45/0.63          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.45/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.45/0.63          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.45/0.63          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.45/0.63          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3)
% 0.45/0.63          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.45/0.63          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.63          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.63          | (v2_struct_0 @ X1)
% 0.45/0.63          | ~ (l1_pre_topc @ X0)
% 0.45/0.63          | ~ (v2_pre_topc @ X0)
% 0.45/0.63          | (v2_struct_0 @ X0))),
% 0.45/0.63      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.45/0.63  thf('114', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          ((v2_struct_0 @ sk_B)
% 0.45/0.63           | ~ (v2_pre_topc @ sk_B)
% 0.45/0.63           | ~ (l1_pre_topc @ sk_B)
% 0.45/0.63           | (v2_struct_0 @ sk_C_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.45/0.63           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.45/0.63           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.45/0.63           | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.45/0.63           | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.45/0.63           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.45/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.45/0.63           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.45/0.63           | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['104', '113'])).
% 0.45/0.63  thf('115', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('117', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('118', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('119', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('120', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('121', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('122', plain,
% 0.45/0.63      ((![X0 : $i]:
% 0.45/0.63          ((v2_struct_0 @ sk_B)
% 0.45/0.63           | (v2_struct_0 @ sk_C_1)
% 0.45/0.63           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.45/0.63           | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.45/0.63           | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.45/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.45/0.63           | (v2_struct_0 @ sk_D_1)
% 0.45/0.63           | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)],
% 0.45/0.63                ['114', '115', '116', '117', '118', '119', '120', '121'])).
% 0.45/0.63  thf('123', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_A)
% 0.45/0.63         | (v2_struct_0 @ sk_D_1)
% 0.45/0.63         | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.45/0.63         | ~ (m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.45/0.63         | ~ (r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ 
% 0.45/0.63              (u1_struct_0 @ sk_C_1))
% 0.45/0.63         | (v2_struct_0 @ sk_C_1)
% 0.45/0.63         | (v2_struct_0 @ sk_B)))
% 0.45/0.63         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.63               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['103', '122'])).
% 0.45/0.63  thf('124', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('125', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['61', '66'])).
% 0.45/0.63  thf('126', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.63          | ~ (v3_pre_topc @ X20 @ X21)
% 0.45/0.63          | (m1_connsp_2 @ (sk_D @ X22 @ X20 @ X21) @ X21 @ X22)
% 0.45/0.63          | ~ (r2_hidden @ X22 @ X20)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.45/0.63          | ~ (l1_pre_topc @ X21)
% 0.45/0.63          | ~ (v2_pre_topc @ X21)
% 0.45/0.64          | (v2_struct_0 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.45/0.64  thf('127', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_struct_0 @ sk_D_1)
% 0.45/0.64          | ~ (v2_pre_topc @ sk_D_1)
% 0.45/0.64          | ~ (l1_pre_topc @ sk_D_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ sk_F)
% 0.45/0.64          | (m1_connsp_2 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_D_1 @ X0)
% 0.45/0.64          | ~ (v3_pre_topc @ sk_F @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['125', '126'])).
% 0.45/0.64  thf('128', plain, ((v2_pre_topc @ sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.45/0.64  thf('129', plain, ((l1_pre_topc @ sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('130', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.45/0.64  thf('131', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_struct_0 @ sk_D_1)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ sk_F)
% 0.45/0.64          | (m1_connsp_2 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_D_1 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      (((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.45/0.64        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.45/0.64        | (v2_struct_0 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['124', '131'])).
% 0.45/0.64  thf('133', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.45/0.64      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      (((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.45/0.64        | (v2_struct_0 @ sk_D_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.64  thf('135', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('136', plain,
% 0.45/0.64      ((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)),
% 0.45/0.64      inference('clc', [status(thm)], ['134', '135'])).
% 0.45/0.64  thf('137', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ X0)
% 0.45/0.64          | ~ (r1_tarski @ sk_F @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.64  thf('139', plain,
% 0.45/0.64      ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ (u1_struct_0 @ sk_C_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['137', '138'])).
% 0.45/0.64  thf('140', plain,
% 0.45/0.64      ((((v2_struct_0 @ sk_A)
% 0.45/0.64         | (v2_struct_0 @ sk_D_1)
% 0.45/0.64         | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.45/0.64         | (v2_struct_0 @ sk_C_1)
% 0.45/0.64         | (v2_struct_0 @ sk_B)))
% 0.45/0.64         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.64      inference('demod', [status(thm)], ['123', '136', '139'])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.45/0.64         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.45/0.64      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('142', plain,
% 0.45/0.64      ((((v2_struct_0 @ sk_B)
% 0.45/0.64         | (v2_struct_0 @ sk_C_1)
% 0.45/0.64         | (v2_struct_0 @ sk_D_1)
% 0.45/0.64         | (v2_struct_0 @ sk_A)))
% 0.45/0.64         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) & 
% 0.45/0.64             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['140', '141'])).
% 0.45/0.64  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('144', plain,
% 0.45/0.64      ((((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.45/0.64         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) & 
% 0.45/0.64             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['142', '143'])).
% 0.45/0.64  thf('145', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('146', plain,
% 0.45/0.64      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.45/0.64         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) & 
% 0.45/0.64             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.64      inference('clc', [status(thm)], ['144', '145'])).
% 0.45/0.64  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('148', plain,
% 0.45/0.64      (((v2_struct_0 @ sk_C_1))
% 0.45/0.64         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) & 
% 0.45/0.64             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.45/0.64      inference('clc', [status(thm)], ['146', '147'])).
% 0.45/0.64  thf('149', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('150', plain,
% 0.45/0.64      (~
% 0.45/0.64       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.45/0.64         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.45/0.64       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.45/0.64      inference('sup-', [status(thm)], ['148', '149'])).
% 0.45/0.64  thf('151', plain, ($false),
% 0.45/0.64      inference('sat_resolution*', [status(thm)],
% 0.45/0.64                ['8', '17', '18', '53', '54', '150'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
