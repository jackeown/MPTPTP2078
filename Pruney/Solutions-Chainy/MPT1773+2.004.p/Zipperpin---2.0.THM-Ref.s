%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fV973riPG4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 730 expanded)
%              Number of leaves         :   35 ( 219 expanded)
%              Depth                    :   26
%              Number of atoms          : 2280 (31971 expanded)
%              Number of equality atoms :   32 ( 412 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t84_tmap_1,conjecture,(
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
                                        <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','28','33','34','35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['3','49'])).

thf('51',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ( X34 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('70',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X31 )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('73',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['64','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('88',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['59'])).

thf('89',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['57'])).

thf('98',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['54','63','96','97'])).

thf('99',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['50','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X37 )
      | ( X37 != X39 )
      | ~ ( r1_tmap_1 @ X36 @ X40 @ ( k2_tmap_1 @ X35 @ X40 @ X41 @ X36 ) @ X39 )
      | ( r1_tmap_1 @ X35 @ X40 @ X41 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('102',plain,(
    ! [X35: $i,X36: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ( r1_tmap_1 @ X35 @ X40 @ X41 @ X39 )
      | ~ ( r1_tmap_1 @ X36 @ X40 @ ( k2_tmap_1 @ X35 @ X40 @ X41 @ X36 ) @ X39 )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X39 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('105',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('106',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','115'])).

thf('117',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('119',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('124',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('125',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_tarski @ sk_F @ sk_F )
      | ( m1_connsp_2 @ sk_F @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('129',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ sk_F @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['127','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F ) ),
    inference('sup-',[status(thm)],['118','130'])).

thf('132',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117','137'])).

thf('139',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('140',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['53'])).

thf('142',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['54','63','96','142'])).

thf('144',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['139','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['0','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fV973riPG4
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 160 iterations in 0.100s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.57  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.57  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.57  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(t84_tmap_1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57             ( l1_pre_topc @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.57                   ( ![E:$i]:
% 0.20/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.57                         ( v1_funct_2 @
% 0.20/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.57                         ( m1_subset_1 @
% 0.20/0.57                           E @ 
% 0.20/0.57                           ( k1_zfmisc_1 @
% 0.20/0.57                             ( k2_zfmisc_1 @
% 0.20/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.57                         ( ![F:$i]:
% 0.20/0.57                           ( ( m1_subset_1 @
% 0.20/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.57                             ( ![G:$i]:
% 0.20/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.57                                 ( ![H:$i]:
% 0.20/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.57                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.57                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.57                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.57                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.57                                         ( r1_tmap_1 @
% 0.20/0.57                                           C @ B @ 
% 0.20/0.57                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.57            ( l1_pre_topc @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57                ( l1_pre_topc @ B ) ) =>
% 0.20/0.57              ( ![C:$i]:
% 0.20/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.57                  ( ![D:$i]:
% 0.20/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.57                      ( ![E:$i]:
% 0.20/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.57                            ( v1_funct_2 @
% 0.20/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.57                            ( m1_subset_1 @
% 0.20/0.57                              E @ 
% 0.20/0.57                              ( k1_zfmisc_1 @
% 0.20/0.57                                ( k2_zfmisc_1 @
% 0.20/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.57                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.57                            ( ![F:$i]:
% 0.20/0.57                              ( ( m1_subset_1 @
% 0.20/0.57                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.57                                ( ![G:$i]:
% 0.20/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.57                                    ( ![H:$i]:
% 0.20/0.57                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.57                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.57                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.57                                            ( r1_tarski @
% 0.20/0.57                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.57                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.57                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.57                                            ( r1_tmap_1 @
% 0.20/0.57                                              C @ B @ 
% 0.20/0.57                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.57                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.20/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.57      inference('split', [status(esa)], ['2'])).
% 0.20/0.57  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('5', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_E @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d5_tmap_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57             ( l1_pre_topc @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.57                   ( ![E:$i]:
% 0.20/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.57                         ( v1_funct_2 @
% 0.20/0.57                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.57                         ( m1_subset_1 @
% 0.20/0.57                           E @ 
% 0.20/0.57                           ( k1_zfmisc_1 @
% 0.20/0.57                             ( k2_zfmisc_1 @
% 0.20/0.57                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.57                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.57                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.57                           ( k2_partfun1 @
% 0.20/0.57                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.57                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X24)
% 0.20/0.57          | ~ (v2_pre_topc @ X24)
% 0.20/0.57          | ~ (l1_pre_topc @ X24)
% 0.20/0.57          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.57          | ~ (m1_pre_topc @ X25 @ X27)
% 0.20/0.57          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.20/0.57                 X28 @ (u1_struct_0 @ X25)))
% 0.20/0.57          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.20/0.57          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.20/0.57          | ~ (v1_funct_1 @ X28)
% 0.20/0.57          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.57          | ~ (l1_pre_topc @ X26)
% 0.20/0.57          | ~ (v2_pre_topc @ X26)
% 0.20/0.57          | (v2_struct_0 @ X26))),
% 0.20/0.57      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X0)
% 0.20/0.57          | ~ (v2_pre_topc @ X0)
% 0.20/0.57          | ~ (l1_pre_topc @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.57               (u1_struct_0 @ sk_B))
% 0.20/0.57          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.57          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X0)
% 0.20/0.57          | ~ (v2_pre_topc @ X0)
% 0.20/0.57          | ~ (l1_pre_topc @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.20/0.57          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.57          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.20/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_B)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ X0 @ sk_E)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57          | (v2_struct_0 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '13'])).
% 0.20/0.57  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_B)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ X0 @ sk_E)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.57          | (v2_struct_0 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.20/0.57            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.57        | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.20/0.57        | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '17'])).
% 0.20/0.57  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_E @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d4_tmap_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57             ( l1_pre_topc @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.57                 ( m1_subset_1 @
% 0.20/0.57                   C @ 
% 0.20/0.57                   ( k1_zfmisc_1 @
% 0.20/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.57                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.57                     ( k2_partfun1 @
% 0.20/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.57                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X20)
% 0.20/0.57          | ~ (v2_pre_topc @ X20)
% 0.20/0.57          | ~ (l1_pre_topc @ X20)
% 0.20/0.57          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.57          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.20/0.57                 X23 @ (u1_struct_0 @ X21)))
% 0.20/0.57          | ~ (m1_subset_1 @ X23 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.20/0.57          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.20/0.57          | ~ (v1_funct_1 @ X23)
% 0.20/0.57          | ~ (l1_pre_topc @ X22)
% 0.20/0.57          | ~ (v2_pre_topc @ X22)
% 0.20/0.57          | (v2_struct_0 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.57               (u1_struct_0 @ sk_B))
% 0.20/0.57          | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(cc1_pre_topc, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.57          | (v2_pre_topc @ X6)
% 0.20/0.57          | ~ (l1_pre_topc @ X7)
% 0.20/0.57          | ~ (v2_pre_topc @ X7))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v2_pre_topc @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('28', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.57  thf('29', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_m1_pre_topc, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i]:
% 0.20/0.57         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.57  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.57  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('33', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0)
% 0.20/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)],
% 0.20/0.57                ['22', '28', '33', '34', '35', '36', '37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_B)
% 0.20/0.57        | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.20/0.57            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['19', '38'])).
% 0.20/0.57  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_D_1)
% 0.20/0.57        | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.20/0.57            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.57      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf('42', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.20/0.57         = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.57            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.20/0.57            = (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C))
% 0.20/0.57        | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['18', '43', '44'])).
% 0.20/0.57  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_B)
% 0.20/0.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.20/0.57            = (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)))),
% 0.20/0.57      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.57  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.20/0.57         = (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C))),
% 0.20/0.57      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ 
% 0.20/0.57         sk_H))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('52', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.20/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.20/0.57       ~
% 0.20/0.57       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.57      inference('split', [status(esa)], ['53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('56', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.20/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.57      inference('split', [status(esa)], ['57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.20/0.57        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.20/0.57         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('split', [status(esa)], ['59'])).
% 0.20/0.57  thf('61', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.20/0.57       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('sup-', [status(thm)], ['58', '62'])).
% 0.20/0.57  thf('64', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('split', [status(esa)], ['2'])).
% 0.20/0.57  thf('66', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_E @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t64_tmap_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57             ( l1_pre_topc @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.57                 ( m1_subset_1 @
% 0.20/0.57                   C @ 
% 0.20/0.57                   ( k1_zfmisc_1 @
% 0.20/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.57                   ( ![E:$i]:
% 0.20/0.57                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.57                       ( ![F:$i]:
% 0.20/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.57                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.57                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.57                             ( r1_tmap_1 @
% 0.20/0.57                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X29)
% 0.20/0.57          | ~ (v2_pre_topc @ X29)
% 0.20/0.57          | ~ (l1_pre_topc @ X29)
% 0.20/0.57          | (v2_struct_0 @ X30)
% 0.20/0.57          | ~ (m1_pre_topc @ X30 @ X29)
% 0.20/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.20/0.57          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.20/0.57          | ((X34) != (X31))
% 0.20/0.57          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.20/0.57          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.20/0.57          | ~ (m1_subset_1 @ X33 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.20/0.57          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.20/0.57          | ~ (v1_funct_1 @ X33)
% 0.20/0.57          | ~ (l1_pre_topc @ X32)
% 0.20/0.57          | ~ (v2_pre_topc @ X32)
% 0.20/0.57          | (v2_struct_0 @ X32))),
% 0.20/0.57      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X32)
% 0.20/0.57          | ~ (v2_pre_topc @ X32)
% 0.20/0.57          | ~ (l1_pre_topc @ X32)
% 0.20/0.57          | ~ (v1_funct_1 @ X33)
% 0.20/0.57          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.20/0.57          | ~ (m1_subset_1 @ X33 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.20/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.57          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.20/0.57          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.20/0.57          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.20/0.57          | ~ (m1_pre_topc @ X30 @ X29)
% 0.20/0.57          | (v2_struct_0 @ X30)
% 0.20/0.57          | ~ (l1_pre_topc @ X29)
% 0.20/0.57          | ~ (v2_pre_topc @ X29)
% 0.20/0.57          | (v2_struct_0 @ X29))),
% 0.20/0.57      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.57          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ 
% 0.20/0.57             X1)
% 0.20/0.57          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.57               (u1_struct_0 @ sk_B))
% 0.20/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.57  thf('72', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.57  thf('73', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('77', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.57          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ 
% 0.20/0.57             X1)
% 0.20/0.57          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)],
% 0.20/0.57                ['71', '72', '73', '74', '75', '76', '77'])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((v2_struct_0 @ sk_B)
% 0.20/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57           | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.57              (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ sk_H)
% 0.20/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.57           | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57           | (v2_struct_0 @ X0)
% 0.20/0.57           | (v2_struct_0 @ sk_D_1)))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['67', '78'])).
% 0.20/0.57  thf('80', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('81', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('82', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.57  thf('83', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((v2_struct_0 @ sk_B)
% 0.20/0.57           | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.57              (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ sk_H)
% 0.20/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.57           | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57           | (v2_struct_0 @ X0)
% 0.20/0.57           | (v2_struct_0 @ sk_D_1)))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['79', '82'])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      ((((v2_struct_0 @ sk_D_1)
% 0.20/0.57         | (v2_struct_0 @ sk_C)
% 0.20/0.57         | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.20/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57            (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.20/0.57         | (v2_struct_0 @ sk_B)))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['64', '83'])).
% 0.20/0.57  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      ((((v2_struct_0 @ sk_D_1)
% 0.20/0.57         | (v2_struct_0 @ sk_C)
% 0.20/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57            (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.20/0.57         | (v2_struct_0 @ sk_B)))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.20/0.57         = (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C))),
% 0.20/0.57      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.57      inference('split', [status(esa)], ['59'])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57           (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_H))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D_1)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['86', '89'])).
% 0.20/0.57  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('92', plain,
% 0.20/0.57      ((((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.57  thf('93', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('94', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_C))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.57  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('96', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.57       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.57  thf('97', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.57       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.20/0.57      inference('split', [status(esa)], ['57'])).
% 0.20/0.57  thf('98', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['54', '63', '96', '97'])).
% 0.20/0.57  thf('99', plain,
% 0.20/0.57      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ 
% 0.20/0.57        sk_H)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['50', '98'])).
% 0.20/0.57  thf('100', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_E @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t65_tmap_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.57             ( l1_pre_topc @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.57                 ( m1_subset_1 @
% 0.20/0.57                   C @ 
% 0.20/0.57                   ( k1_zfmisc_1 @
% 0.20/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.57                   ( ![E:$i]:
% 0.20/0.57                     ( ( m1_subset_1 @
% 0.20/0.57                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.57                       ( ![F:$i]:
% 0.20/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.57                           ( ![G:$i]:
% 0.20/0.57                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.57                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.57                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.57                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.57                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.57                                   ( r1_tmap_1 @
% 0.20/0.57                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('101', plain,
% 0.20/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X35)
% 0.20/0.57          | ~ (v2_pre_topc @ X35)
% 0.20/0.57          | ~ (l1_pre_topc @ X35)
% 0.20/0.57          | (v2_struct_0 @ X36)
% 0.20/0.57          | ~ (m1_pre_topc @ X36 @ X35)
% 0.20/0.57          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.20/0.57          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.20/0.57          | ~ (m1_connsp_2 @ X38 @ X35 @ X37)
% 0.20/0.57          | ((X37) != (X39))
% 0.20/0.57          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.20/0.57               X39)
% 0.20/0.57          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X37)
% 0.20/0.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.20/0.57          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.57          | ~ (m1_subset_1 @ X41 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.20/0.57          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.20/0.57          | ~ (v1_funct_1 @ X41)
% 0.20/0.57          | ~ (l1_pre_topc @ X40)
% 0.20/0.57          | ~ (v2_pre_topc @ X40)
% 0.20/0.57          | (v2_struct_0 @ X40))),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.57  thf('102', plain,
% 0.20/0.57      (![X35 : $i, X36 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.57         ((v2_struct_0 @ X40)
% 0.20/0.57          | ~ (v2_pre_topc @ X40)
% 0.20/0.57          | ~ (l1_pre_topc @ X40)
% 0.20/0.57          | ~ (v1_funct_1 @ X41)
% 0.20/0.57          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))
% 0.20/0.57          | ~ (m1_subset_1 @ X41 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X40))))
% 0.20/0.57          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.20/0.57          | (r1_tmap_1 @ X35 @ X40 @ X41 @ X39)
% 0.20/0.57          | ~ (r1_tmap_1 @ X36 @ X40 @ (k2_tmap_1 @ X35 @ X40 @ X41 @ X36) @ 
% 0.20/0.57               X39)
% 0.20/0.57          | ~ (m1_connsp_2 @ X38 @ X35 @ X39)
% 0.20/0.57          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X36))
% 0.20/0.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.20/0.57          | ~ (m1_pre_topc @ X36 @ X35)
% 0.20/0.57          | (v2_struct_0 @ X36)
% 0.20/0.57          | ~ (l1_pre_topc @ X35)
% 0.20/0.57          | ~ (v2_pre_topc @ X35)
% 0.20/0.57          | (v2_struct_0 @ X35))),
% 0.20/0.57      inference('simplify', [status(thm)], ['101'])).
% 0.20/0.57  thf('103', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.57          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X1)
% 0.20/0.57          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.57               (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ X1)
% 0.20/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.20/0.57               (u1_struct_0 @ sk_B))
% 0.20/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['100', '102'])).
% 0.20/0.57  thf('104', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.57  thf('105', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf('106', plain,
% 0.20/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('107', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('110', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ X0)
% 0.20/0.57          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.57          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X1)
% 0.20/0.57          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.57               (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0) @ X1)
% 0.20/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X1)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)],
% 0.20/0.57                ['103', '104', '105', '106', '107', '108', '109'])).
% 0.20/0.57  thf('111', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.20/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.20/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.57          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.20/0.57          | (v2_struct_0 @ sk_C)
% 0.20/0.57          | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['99', '110'])).
% 0.20/0.57  thf('112', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('113', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.57  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('115', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.20/0.57          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.20/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.57          | (v2_struct_0 @ sk_C)
% 0.20/0.57          | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.20/0.57  thf('116', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_D_1)
% 0.20/0.57        | (v2_struct_0 @ sk_C)
% 0.20/0.57        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.57        | ~ (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)
% 0.20/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.20/0.57        | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '115'])).
% 0.20/0.57  thf('117', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('118', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.57  thf('119', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('120', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t8_connsp_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.57                 ( ?[D:$i]:
% 0.20/0.57                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.57                     ( v3_pre_topc @ D @ A ) & 
% 0.20/0.57                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('121', plain,
% 0.20/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.57          | ~ (r2_hidden @ X16 @ X19)
% 0.20/0.57          | ~ (r1_tarski @ X19 @ X18)
% 0.20/0.57          | ~ (v3_pre_topc @ X19 @ X17)
% 0.20/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.57          | (m1_connsp_2 @ X18 @ X17 @ X16)
% 0.20/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.57          | ~ (l1_pre_topc @ X17)
% 0.20/0.57          | ~ (v2_pre_topc @ X17)
% 0.20/0.57          | (v2_struct_0 @ X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.57  thf('122', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ~ (v2_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (l1_pre_topc @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.20/0.57          | ~ (v3_pre_topc @ sk_F @ sk_D_1)
% 0.20/0.57          | ~ (r1_tarski @ sk_F @ X0)
% 0.20/0.57          | ~ (r2_hidden @ X1 @ sk_F)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.57  thf('123', plain, ((v2_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.57  thf('124', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf('125', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('126', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v2_struct_0 @ sk_D_1)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.57          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.20/0.57          | ~ (r1_tarski @ sk_F @ X0)
% 0.20/0.57          | ~ (r2_hidden @ X1 @ sk_F)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.57      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 0.20/0.57  thf('127', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_F)
% 0.20/0.57          | ~ (r1_tarski @ sk_F @ sk_F)
% 0.20/0.57          | (m1_connsp_2 @ sk_F @ sk_D_1 @ X0)
% 0.20/0.57          | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['119', '126'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('128', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('129', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.57      inference('simplify', [status(thm)], ['128'])).
% 0.20/0.57  thf('130', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_F)
% 0.20/0.57          | (m1_connsp_2 @ sk_F @ sk_D_1 @ X0)
% 0.20/0.57          | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('demod', [status(thm)], ['127', '129'])).
% 0.20/0.57  thf('131', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_D_1)
% 0.20/0.57        | (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)
% 0.20/0.57        | ~ (r2_hidden @ sk_H @ sk_F))),
% 0.20/0.57      inference('sup-', [status(thm)], ['118', '130'])).
% 0.20/0.57  thf('132', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('133', plain, (((sk_G) = (sk_H))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('134', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.57      inference('demod', [status(thm)], ['132', '133'])).
% 0.20/0.57  thf('135', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_D_1) | (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H))),
% 0.20/0.57      inference('demod', [status(thm)], ['131', '134'])).
% 0.20/0.57  thf('136', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('137', plain, ((m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)),
% 0.20/0.57      inference('clc', [status(thm)], ['135', '136'])).
% 0.20/0.57  thf('138', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_D_1)
% 0.20/0.57        | (v2_struct_0 @ sk_C)
% 0.20/0.57        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.20/0.57        | (v2_struct_0 @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['116', '117', '137'])).
% 0.20/0.57  thf('139', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('140', plain,
% 0.20/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.57  thf('141', plain,
% 0.20/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.20/0.57         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.57      inference('split', [status(esa)], ['53'])).
% 0.20/0.57  thf('142', plain,
% 0.20/0.57      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)) | 
% 0.20/0.57       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.20/0.57      inference('sup-', [status(thm)], ['140', '141'])).
% 0.20/0.57  thf('143', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['54', '63', '96', '142'])).
% 0.20/0.57  thf('144', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['139', '143'])).
% 0.20/0.57  thf('145', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['138', '144'])).
% 0.20/0.57  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('147', plain, (((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C))),
% 0.20/0.57      inference('clc', [status(thm)], ['145', '146'])).
% 0.20/0.57  thf('148', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('149', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.57      inference('clc', [status(thm)], ['147', '148'])).
% 0.20/0.57  thf('150', plain, ($false), inference('demod', [status(thm)], ['0', '149'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
