%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q2Yy2xgztG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 971 expanded)
%              Number of leaves         :   35 ( 289 expanded)
%              Depth                    :   30
%              Number of atoms          : 2436 (41088 expanded)
%              Number of equality atoms :   39 ( 550 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
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
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
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
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','28','33','34','35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['3','49'])).

thf('51',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X23 @ X20 @ X22 )
      | ( X22 != X24 )
      | ~ ( r1_tmap_1 @ X20 @ X25 @ X26 @ X22 )
      | ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ~ ( r1_tmap_1 @ X20 @ X25 @ X26 @ X24 )
      | ~ ( m1_connsp_2 @ X23 @ X20 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('66',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('78',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_tops_1 @ X9 @ X10 ) )
      | ( m1_connsp_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('83',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('85',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
   <= ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['84'])).

thf('88',plain,
    ( ( ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('91',plain,(
    ~ ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
    | ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['84'])).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference(simpl_trail,[status(thm)],['85','93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_D @ sk_F )
      = sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_D @ sk_F )
    = sk_F ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','98'])).

thf('100',plain,
    ( ~ ( r2_hidden @ sk_H @ sk_F )
    | ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','99'])).

thf('101',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['73','76','106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['55','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['58'])).

thf('124',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['54','122','123'])).

thf('125',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['50','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X23 @ X20 @ X22 )
      | ( X22 != X24 )
      | ~ ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ( r1_tmap_1 @ X20 @ X25 @ X26 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('128',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X20 @ X25 @ X26 @ X24 )
      | ~ ( r1_tmap_1 @ X21 @ X25 @ ( k2_tmap_1 @ X20 @ X25 @ X26 @ X21 ) @ X24 )
      | ~ ( m1_connsp_2 @ X23 @ X20 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('131',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('132',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['125','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('140',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','141'])).

thf('143',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['104','105'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['113'])).

thf('147',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('150',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['53'])).

thf('153',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['54','122','153'])).

thf('155',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['148','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['145','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['0','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q2Yy2xgztG
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:12 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 86 iterations in 0.048s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(t84_tmap_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.51                         ( ![F:$i]:
% 0.20/0.51                           ( ( m1_subset_1 @
% 0.20/0.51                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.51                             ( ![G:$i]:
% 0.20/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                 ( ![H:$i]:
% 0.20/0.51                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.51                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.51                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.51                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.51                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.51                                         ( r1_tmap_1 @
% 0.20/0.51                                           C @ B @ 
% 0.20/0.51                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.51                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51                ( l1_pre_topc @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                      ( ![E:$i]:
% 0.20/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                            ( v1_funct_2 @
% 0.20/0.51                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                            ( m1_subset_1 @
% 0.20/0.51                              E @ 
% 0.20/0.51                              ( k1_zfmisc_1 @
% 0.20/0.51                                ( k2_zfmisc_1 @
% 0.20/0.51                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.51                            ( ![F:$i]:
% 0.20/0.51                              ( ( m1_subset_1 @
% 0.20/0.51                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.51                                ( ![G:$i]:
% 0.20/0.51                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                    ( ![H:$i]:
% 0.20/0.51                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.51                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.51                                            ( r1_tarski @
% 0.20/0.51                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.51                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.51                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.51                                            ( r1_tmap_1 @
% 0.20/0.51                                              C @ B @ 
% 0.20/0.51                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.51                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d5_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.51                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.51                           ( k2_partfun1 @
% 0.20/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.51                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | ~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.51          | ~ (m1_pre_topc @ X16 @ X18)
% 0.20/0.51          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.20/0.51                 X19 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.20/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (m1_pre_topc @ X18 @ X17)
% 0.20/0.51          | ~ (l1_pre_topc @ X17)
% 0.20/0.51          | ~ (v2_pre_topc @ X17)
% 0.20/0.51          | (v2_struct_0 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '13'])).
% 0.20/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.51        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '17'])).
% 0.20/0.51  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d4_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.51                     ( k2_partfun1 @
% 0.20/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | ~ (l1_pre_topc @ X11)
% 0.20/0.51          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.20/0.51                 X14 @ (u1_struct_0 @ X12)))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.20/0.51          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.20/0.51          | ~ (v1_funct_1 @ X14)
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (v2_pre_topc @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.51          | (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X1)
% 0.20/0.51          | ~ (v2_pre_topc @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['22', '28', '33', '34', '35', '36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.51        | (v2_struct_0 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '38'])).
% 0.20/0.51  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_D)
% 0.20/0.51        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.51            (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.51            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '43', '44'])).
% 0.20/0.51  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.51            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.20/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.51         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.20/0.51         sk_H))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, (((sk_G) = (sk_H))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.51      inference('split', [status(esa)], ['53'])).
% 0.20/0.51  thf('55', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, (((sk_G) = (sk_H))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('split', [status(esa)], ['58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t65_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( m1_subset_1 @
% 0.20/0.51                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                       ( ![F:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                           ( ![G:$i]:
% 0.20/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.51                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.20/0.51                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.51                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.51                                   ( r1_tmap_1 @
% 0.20/0.51                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X20)
% 0.20/0.51          | ~ (v2_pre_topc @ X20)
% 0.20/0.51          | ~ (l1_pre_topc @ X20)
% 0.20/0.51          | (v2_struct_0 @ X21)
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.20/0.51          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.51          | ~ (m1_connsp_2 @ X23 @ X20 @ X22)
% 0.20/0.51          | ((X22) != (X24))
% 0.20/0.51          | ~ (r1_tmap_1 @ X20 @ X25 @ X26 @ X22)
% 0.20/0.51          | (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ X24)
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.20/0.51          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.20/0.51          | ~ (v1_funct_1 @ X26)
% 0.20/0.51          | ~ (l1_pre_topc @ X25)
% 0.20/0.51          | ~ (v2_pre_topc @ X25)
% 0.20/0.51          | (v2_struct_0 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X25)
% 0.20/0.51          | ~ (v2_pre_topc @ X25)
% 0.20/0.51          | ~ (l1_pre_topc @ X25)
% 0.20/0.51          | ~ (v1_funct_1 @ X26)
% 0.20/0.51          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.20/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.20/0.51          | (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ X24)
% 0.20/0.51          | ~ (r1_tmap_1 @ X20 @ X25 @ X26 @ X24)
% 0.20/0.51          | ~ (m1_connsp_2 @ X23 @ X20 @ X24)
% 0.20/0.51          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.20/0.51          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.51          | (v2_struct_0 @ X21)
% 0.20/0.51          | ~ (l1_pre_topc @ X20)
% 0.20/0.51          | ~ (v2_pre_topc @ X20)
% 0.20/0.51          | (v2_struct_0 @ X20))),
% 0.20/0.51      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['61', '63'])).
% 0.20/0.51  thf('65', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('66', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['64', '65', '66', '67', '68', '69', '70'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.20/0.51          | ~ (m1_connsp_2 @ sk_F @ sk_D @ X1)
% 0.20/0.51          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_D)
% 0.20/0.51           | (v2_struct_0 @ X0)
% 0.20/0.51           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.51           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.51           | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.51           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.20/0.51              sk_H)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.51           | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '72'])).
% 0.20/0.51  thf('74', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain, (((sk_G) = (sk_H))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('76', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d1_connsp_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.51                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (r2_hidden @ X8 @ (k1_tops_1 @ X9 @ X10))
% 0.20/0.51          | (m1_connsp_2 @ X10 @ X9 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.51          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_D @ sk_F))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t55_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( l1_pre_topc @ B ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.51                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.51                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.51                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51          | ((k1_tops_1 @ X4 @ X5) = (X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51          | ~ (l1_pre_topc @ X7)
% 0.20/0.51          | ~ (v2_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((![X4 : $i, X5 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ X4)
% 0.20/0.51           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51           | ((k1_tops_1 @ X4 @ X5) = (X5))))
% 0.20/0.51         <= ((![X4 : $i, X5 : $i]:
% 0.20/0.51                (~ (l1_pre_topc @ X4)
% 0.20/0.51                 | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51                 | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51                 | ((k1_tops_1 @ X4 @ X5) = (X5)))))),
% 0.20/0.51      inference('split', [status(esa)], ['84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((![X6 : $i, X7 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51           | ~ (l1_pre_topc @ X7)
% 0.20/0.51           | ~ (v2_pre_topc @ X7)))
% 0.20/0.51         <= ((![X6 : $i, X7 : $i]:
% 0.20/0.51                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51                 | ~ (l1_pre_topc @ X7)
% 0.20/0.51                 | ~ (v2_pre_topc @ X7))))),
% 0.20/0.51      inference('split', [status(esa)], ['84'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (((~ (v2_pre_topc @ sk_D) | ~ (l1_pre_topc @ sk_D)))
% 0.20/0.51         <= ((![X6 : $i, X7 : $i]:
% 0.20/0.51                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51                 | ~ (l1_pre_topc @ X7)
% 0.20/0.51                 | ~ (v2_pre_topc @ X7))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.51  thf('89', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.51  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (~
% 0.20/0.51       (![X6 : $i, X7 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51           | ~ (l1_pre_topc @ X7)
% 0.20/0.51           | ~ (v2_pre_topc @ X7)))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      ((![X4 : $i, X5 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ X4)
% 0.20/0.51           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51           | ((k1_tops_1 @ X4 @ X5) = (X5)))) | 
% 0.20/0.51       (![X6 : $i, X7 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51           | ~ (l1_pre_topc @ X7)
% 0.20/0.51           | ~ (v2_pre_topc @ X7)))),
% 0.20/0.51      inference('split', [status(esa)], ['84'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((![X4 : $i, X5 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ X4)
% 0.20/0.51           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51           | ((k1_tops_1 @ X4 @ X5) = (X5))))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.51          | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.51          | ((k1_tops_1 @ X4 @ X5) = (X5)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['85', '93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      ((((k1_tops_1 @ sk_D @ sk_F) = (sk_F))
% 0.20/0.51        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['83', '94'])).
% 0.20/0.51  thf('96', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('98', plain, (((k1_tops_1 @ sk_D @ sk_F) = (sk_F))),
% 0.20/0.51      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_D)
% 0.20/0.51          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_F)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['80', '81', '82', '98'])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.51        | (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.51        | (v2_struct_0 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['77', '99'])).
% 0.20/0.51  thf('101', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, (((sk_G) = (sk_H))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.51      inference('demod', [status(thm)], ['101', '102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (((m1_connsp_2 @ sk_F @ sk_D @ sk_H) | (v2_struct_0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['100', '103'])).
% 0.20/0.51  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('106', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.20/0.51      inference('clc', [status(thm)], ['104', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_D)
% 0.20/0.51           | (v2_struct_0 @ X0)
% 0.20/0.51           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.51           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.20/0.51              sk_H)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.51           | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('demod', [status(thm)], ['73', '76', '106'])).
% 0.20/0.51  thf('108', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.51         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.20/0.51         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.51         | (v2_struct_0 @ sk_C)
% 0.20/0.51         | (v2_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '107'])).
% 0.20/0.51  thf('109', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('110', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.20/0.51         | (v2_struct_0 @ sk_C)
% 0.20/0.51         | (v2_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.51         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('split', [status(esa)], ['113'])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.20/0.51           sk_H))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['112', '114'])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['111', '115'])).
% 0.20/0.51  thf('117', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('118', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('clc', [status(thm)], ['116', '117'])).
% 0.20/0.51  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.51      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.51  thf('121', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('122', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.51       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.20/0.51      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.51  thf('123', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.51         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.51       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.20/0.52      inference('split', [status(esa)], ['58'])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['54', '122', '123'])).
% 0.20/0.52  thf('125', plain,
% 0.20/0.52      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.20/0.52        sk_H)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['50', '124'])).
% 0.20/0.52  thf('126', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_E @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('127', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X20)
% 0.20/0.52          | ~ (v2_pre_topc @ X20)
% 0.20/0.52          | ~ (l1_pre_topc @ X20)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.20/0.52          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.52          | ~ (m1_connsp_2 @ X23 @ X20 @ X22)
% 0.20/0.52          | ((X22) != (X24))
% 0.20/0.52          | ~ (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ 
% 0.20/0.52               X24)
% 0.20/0.52          | (r1_tmap_1 @ X20 @ X25 @ X26 @ X22)
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.20/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.20/0.52          | ~ (v1_funct_1 @ X26)
% 0.20/0.52          | ~ (l1_pre_topc @ X25)
% 0.20/0.52          | ~ (v2_pre_topc @ X25)
% 0.20/0.52          | (v2_struct_0 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.20/0.52  thf('128', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X25)
% 0.20/0.52          | ~ (v2_pre_topc @ X25)
% 0.20/0.52          | ~ (l1_pre_topc @ X25)
% 0.20/0.52          | ~ (v1_funct_1 @ X26)
% 0.20/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))
% 0.20/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X25))))
% 0.20/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X21))
% 0.20/0.52          | (r1_tmap_1 @ X20 @ X25 @ X26 @ X24)
% 0.20/0.52          | ~ (r1_tmap_1 @ X21 @ X25 @ (k2_tmap_1 @ X20 @ X25 @ X26 @ X21) @ 
% 0.20/0.52               X24)
% 0.20/0.52          | ~ (m1_connsp_2 @ X23 @ X20 @ X24)
% 0.20/0.52          | ~ (r1_tarski @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.20/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (l1_pre_topc @ X20)
% 0.20/0.52          | ~ (v2_pre_topc @ X20)
% 0.20/0.52          | (v2_struct_0 @ X20))),
% 0.20/0.52      inference('simplify', [status(thm)], ['127'])).
% 0.20/0.52  thf('129', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.20/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.20/0.52               X1)
% 0.20/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['126', '128'])).
% 0.20/0.52  thf('130', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.52  thf('131', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('132', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('133', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('134', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('135', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.20/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.20/0.52               X1)
% 0.20/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['129', '130', '131', '132', '133', '134', '135'])).
% 0.20/0.52  thf('137', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.52          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['125', '136'])).
% 0.20/0.52  thf('138', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('139', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('140', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('141', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.52          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.52          | (v2_struct_0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.20/0.52  thf('142', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_C)
% 0.20/0.52        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.52        | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '141'])).
% 0.20/0.52  thf('143', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('144', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.20/0.52      inference('clc', [status(thm)], ['104', '105'])).
% 0.20/0.52  thf('145', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_C)
% 0.20/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.20/0.52  thf('146', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.20/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['113'])).
% 0.20/0.52  thf('147', plain, (((sk_G) = (sk_H))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('148', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.52      inference('demod', [status(thm)], ['146', '147'])).
% 0.20/0.52  thf('149', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('150', plain, (((sk_G) = (sk_H))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('151', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.52      inference('demod', [status(thm)], ['149', '150'])).
% 0.20/0.52  thf('152', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.20/0.52      inference('split', [status(esa)], ['53'])).
% 0.20/0.52  thf('153', plain,
% 0.20/0.52      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) | 
% 0.20/0.52       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.20/0.52      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.52  thf('154', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['54', '122', '153'])).
% 0.20/0.52  thf('155', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['148', '154'])).
% 0.20/0.52  thf('156', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['145', '155'])).
% 0.20/0.52  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('158', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('clc', [status(thm)], ['156', '157'])).
% 0.20/0.52  thf('159', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('160', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('clc', [status(thm)], ['158', '159'])).
% 0.20/0.52  thf('161', plain, ($false), inference('demod', [status(thm)], ['0', '160'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
