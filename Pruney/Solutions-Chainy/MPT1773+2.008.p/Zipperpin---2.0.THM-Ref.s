%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oUhunOZlBE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 842 expanded)
%              Number of leaves         :   33 ( 251 expanded)
%              Depth                    :   26
%              Number of atoms          : 2258 (36953 expanded)
%              Number of equality atoms :   29 ( 468 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X14 )
      | ( ( k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) @ X15 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( k2_tmap_1 @ X9 @ X7 @ X10 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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

thf('55',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X18 )
      | ( X18 != X20 )
      | ~ ( r1_tmap_1 @ X16 @ X21 @ X22 @ X18 )
      | ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ~ ( r1_tmap_1 @ X16 @ X21 @ X22 @ X20 )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
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
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
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
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,
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
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('86',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('87',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( m1_connsp_2 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('91',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ sk_H @ sk_F )
    | ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['81','84','99'])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['64','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['59'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['57'])).

thf('116',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['54','63','114','115'])).

thf('117',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['50','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X18 )
      | ( X18 != X20 )
      | ~ ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ( r1_tmap_1 @ X16 @ X21 @ X22 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('120',plain,(
    ! [X16: $i,X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tmap_1 @ X16 @ X21 @ X22 @ X20 )
      | ~ ( r1_tmap_1 @ X17 @ X21 @ ( k2_tmap_1 @ X16 @ X21 @ X22 @ X17 ) @ X20 )
      | ~ ( m1_connsp_2 @ X19 @ X16 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
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
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('123',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('124',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
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
    inference(demod,[status(thm)],['121','122','123','124','125','126','127'])).

thf('129',plain,(
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
    inference('sup-',[status(thm)],['117','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','133'])).

thf('135',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['97','98'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('139',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('140',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['53'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['54','63','114','141'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['138','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['0','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oUhunOZlBE
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:28:25 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 71 iterations in 0.044s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.22/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_H_type, type, sk_H: $i).
% 0.22/0.53  thf(t84_tmap_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.53                         ( ![F:$i]:
% 0.22/0.53                           ( ( m1_subset_1 @
% 0.22/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.22/0.53                             ( ![G:$i]:
% 0.22/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                                 ( ![H:$i]:
% 0.22/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.22/0.53                                         ( r2_hidden @ G @ F ) & 
% 0.22/0.53                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.22/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.22/0.53                                         ( r1_tmap_1 @
% 0.22/0.53                                           C @ B @ 
% 0.22/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.22/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53            ( l1_pre_topc @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53                ( l1_pre_topc @ B ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53                  ( ![D:$i]:
% 0.22/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.53                      ( ![E:$i]:
% 0.22/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                            ( v1_funct_2 @
% 0.22/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                            ( m1_subset_1 @
% 0.22/0.53                              E @ 
% 0.22/0.53                              ( k1_zfmisc_1 @
% 0.22/0.53                                ( k2_zfmisc_1 @
% 0.22/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                          ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.53                            ( ![F:$i]:
% 0.22/0.53                              ( ( m1_subset_1 @
% 0.22/0.53                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.22/0.53                                ( ![G:$i]:
% 0.22/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                                    ( ![H:$i]:
% 0.22/0.53                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.22/0.53                                            ( r2_hidden @ G @ F ) & 
% 0.22/0.53                                            ( r1_tarski @
% 0.22/0.53                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.53                                            ( ( G ) = ( H ) ) ) =>
% 0.22/0.53                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.22/0.53                                            ( r1_tmap_1 @
% 0.22/0.53                                              C @ B @ 
% 0.22/0.53                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.22/0.53                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.22/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('5', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d5_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                       ( ( m1_pre_topc @ D @ C ) =>
% 0.22/0.53                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.53                           ( k2_partfun1 @
% 0.22/0.53                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.22/0.53                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X11)
% 0.22/0.53          | ~ (v2_pre_topc @ X11)
% 0.22/0.53          | ~ (l1_pre_topc @ X11)
% 0.22/0.53          | ~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.53          | ~ (m1_pre_topc @ X12 @ X14)
% 0.22/0.53          | ((k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 0.22/0.53                 X15 @ (u1_struct_0 @ X12)))
% 0.22/0.53          | ~ (m1_subset_1 @ X15 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))))
% 0.22/0.53          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))
% 0.22/0.53          | ~ (v1_funct_1 @ X15)
% 0.22/0.53          | ~ (m1_pre_topc @ X14 @ X13)
% 0.22/0.53          | ~ (l1_pre_topc @ X13)
% 0.22/0.53          | ~ (v2_pre_topc @ X13)
% 0.22/0.53          | (v2_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X0)
% 0.22/0.53          | ~ (v2_pre_topc @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X0)
% 0.22/0.53          | ~ (v2_pre_topc @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '13'])).
% 0.22/0.53  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.53        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '17'])).
% 0.22/0.53  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d4_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                 ( m1_subset_1 @
% 0.22/0.53                   C @ 
% 0.22/0.53                   ( k1_zfmisc_1 @
% 0.22/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.53                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.53                     ( k2_partfun1 @
% 0.22/0.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.53                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X7)
% 0.22/0.53          | ~ (v2_pre_topc @ X7)
% 0.22/0.53          | ~ (l1_pre_topc @ X7)
% 0.22/0.53          | ~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.53          | ((k2_tmap_1 @ X9 @ X7 @ X10 @ X8)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10 @ 
% 0.22/0.53                 (u1_struct_0 @ X8)))
% 0.22/0.53          | ~ (m1_subset_1 @ X10 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.22/0.53          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.22/0.53          | ~ (v1_funct_1 @ X10)
% 0.22/0.53          | ~ (l1_pre_topc @ X9)
% 0.22/0.53          | ~ (v2_pre_topc @ X9)
% 0.22/0.53          | (v2_struct_0 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc1_pre_topc, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.53          | (v2_pre_topc @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ X1)
% 0.22/0.53          | ~ (v2_pre_topc @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.53  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_m1_pre_topc, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_pre_topc @ A ) =>
% 0.22/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.53  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)],
% 0.22/0.53                ['22', '28', '33', '34', '35', '36', '37'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.22/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.53        | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['19', '38'])).
% 0.22/0.53  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_D)
% 0.22/0.53        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.22/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.22/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.22/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53            (u1_struct_0 @ sk_C)))),
% 0.22/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['18', '43', '44'])).
% 0.22/0.53  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.22/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.53  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.22/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.22/0.53         sk_H))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '49'])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('52', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.22/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) | 
% 0.22/0.53       ~
% 0.22/0.53       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.22/0.53      inference('split', [status(esa)], ['53'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('56', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.22/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.22/0.53      inference('split', [status(esa)], ['57'])).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('61', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) | 
% 0.22/0.53       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('sup-', [status(thm)], ['58', '62'])).
% 0.22/0.53  thf('64', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('65', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf('66', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('67', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t65_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.53                 ( m1_subset_1 @
% 0.22/0.53                   C @ 
% 0.22/0.53                   ( k1_zfmisc_1 @
% 0.22/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( m1_subset_1 @
% 0.22/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                       ( ![F:$i]:
% 0.22/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.53                           ( ![G:$i]:
% 0.22/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.53                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.22/0.53                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.53                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.53                                   ( r1_tmap_1 @
% 0.22/0.53                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('70', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X18)
% 0.22/0.53          | ((X18) != (X20))
% 0.22/0.53          | ~ (r1_tmap_1 @ X16 @ X21 @ X22 @ X18)
% 0.22/0.53          | (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ X20)
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | (v2_struct_0 @ X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.22/0.53  thf('71', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ X20)
% 0.22/0.53          | ~ (r1_tmap_1 @ X16 @ X21 @ X22 @ X20)
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X20)
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X16))),
% 0.22/0.53      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.53  thf('72', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.22/0.53          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['69', '71'])).
% 0.22/0.53  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.53  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('79', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.22/0.53          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)],
% 0.22/0.53                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.22/0.53  thf('80', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.22/0.53          | ~ (m1_connsp_2 @ sk_F @ sk_D @ X1)
% 0.22/0.53          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['68', '79'])).
% 0.22/0.53  thf('81', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((v2_struct_0 @ sk_D)
% 0.22/0.53           | (v2_struct_0 @ X0)
% 0.22/0.53           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.22/0.53           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.53           | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.22/0.53           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.22/0.53              sk_H)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.22/0.53           | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['67', '80'])).
% 0.22/0.53  thf('82', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('83', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('84', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.53  thf('85', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.53  thf('86', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t5_connsp_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.22/0.53                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.22/0.53  thf('87', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.22/0.53          | ~ (v3_pre_topc @ X4 @ X5)
% 0.22/0.53          | ~ (r2_hidden @ X6 @ X4)
% 0.22/0.53          | (m1_connsp_2 @ X4 @ X5 @ X6)
% 0.22/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.53          | ~ (l1_pre_topc @ X5)
% 0.22/0.53          | ~ (v2_pre_topc @ X5)
% 0.22/0.53          | (v2_struct_0 @ X5))),
% 0.22/0.53      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.22/0.53  thf('88', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.22/0.53          | ~ (v3_pre_topc @ sk_F @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.53  thf('89', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.53  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('91', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('92', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.22/0.53  thf('93', plain,
% 0.22/0.53      ((~ (r2_hidden @ sk_H @ sk_F)
% 0.22/0.53        | (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.22/0.53        | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['85', '92'])).
% 0.22/0.53  thf('94', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('95', plain, (((sk_G) = (sk_H))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('96', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.22/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.53  thf('97', plain,
% 0.22/0.53      (((m1_connsp_2 @ sk_F @ sk_D @ sk_H) | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['93', '96'])).
% 0.22/0.53  thf('98', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('99', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.22/0.53      inference('clc', [status(thm)], ['97', '98'])).
% 0.22/0.53  thf('100', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((v2_struct_0 @ sk_D)
% 0.22/0.53           | (v2_struct_0 @ X0)
% 0.22/0.53           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.53           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.22/0.53              sk_H)
% 0.22/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.22/0.53           | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['81', '84', '99'])).
% 0.22/0.53  thf('101', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B)
% 0.22/0.53         | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.22/0.53         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.22/0.53         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.53         | (v2_struct_0 @ sk_C)
% 0.22/0.53         | (v2_struct_0 @ sk_D)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['64', '100'])).
% 0.22/0.53  thf('102', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('103', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('104', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B)
% 0.22/0.53         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.22/0.53         | (v2_struct_0 @ sk_C)
% 0.22/0.53         | (v2_struct_0 @ sk_D)))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.22/0.53  thf('105', plain,
% 0.22/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.22/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.53  thf('106', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('107', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.22/0.53           sk_H))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['105', '106'])).
% 0.22/0.53  thf('108', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['104', '107'])).
% 0.22/0.53  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('110', plain,
% 0.22/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('clc', [status(thm)], ['108', '109'])).
% 0.22/0.53  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('112', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_C))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.22/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('clc', [status(thm)], ['110', '111'])).
% 0.22/0.53  thf('113', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('114', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.22/0.53       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.53      inference('sup-', [status(thm)], ['112', '113'])).
% 0.22/0.53  thf('115', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.22/0.53       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.22/0.53      inference('split', [status(esa)], ['57'])).
% 0.22/0.53  thf('116', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['54', '63', '114', '115'])).
% 0.22/0.53  thf('117', plain,
% 0.22/0.53      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.22/0.53        sk_H)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['50', '116'])).
% 0.22/0.53  thf('118', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('119', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X18)
% 0.22/0.53          | ((X18) != (X20))
% 0.22/0.53          | ~ (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ 
% 0.22/0.53               X20)
% 0.22/0.53          | (r1_tmap_1 @ X16 @ X21 @ X22 @ X18)
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | (v2_struct_0 @ X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.22/0.53  thf('120', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X21)
% 0.22/0.53          | ~ (v2_pre_topc @ X21)
% 0.22/0.53          | ~ (l1_pre_topc @ X21)
% 0.22/0.53          | ~ (v1_funct_1 @ X22)
% 0.22/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))
% 0.22/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X21))))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.22/0.53          | (r1_tmap_1 @ X16 @ X21 @ X22 @ X20)
% 0.22/0.53          | ~ (r1_tmap_1 @ X17 @ X21 @ (k2_tmap_1 @ X16 @ X21 @ X22 @ X17) @ 
% 0.22/0.53               X20)
% 0.22/0.53          | ~ (m1_connsp_2 @ X19 @ X16 @ X20)
% 0.22/0.53          | ~ (r1_tarski @ X19 @ (u1_struct_0 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | (v2_struct_0 @ X17)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X16))),
% 0.22/0.53      inference('simplify', [status(thm)], ['119'])).
% 0.22/0.53  thf('121', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.22/0.53               X1)
% 0.22/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['118', '120'])).
% 0.22/0.53  thf('122', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.53  thf('123', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('124', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('127', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('128', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X1)
% 0.22/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.22/0.53               X1)
% 0.22/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.22/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)],
% 0.22/0.53                ['121', '122', '123', '124', '125', '126', '127'])).
% 0.22/0.53  thf('129', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.22/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.22/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.53          | (v2_struct_0 @ sk_C)
% 0.22/0.53          | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['117', '128'])).
% 0.22/0.53  thf('130', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('131', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.22/0.53  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('133', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.22/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.53          | (v2_struct_0 @ sk_C)
% 0.22/0.53          | (v2_struct_0 @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.22/0.53  thf('134', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_D)
% 0.22/0.53        | (v2_struct_0 @ sk_C)
% 0.22/0.53        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.53        | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '133'])).
% 0.22/0.53  thf('135', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('136', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.22/0.53      inference('clc', [status(thm)], ['97', '98'])).
% 0.22/0.53  thf('137', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_D)
% 0.22/0.53        | (v2_struct_0 @ sk_C)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.22/0.53  thf('138', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.53  thf('139', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('140', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.22/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.22/0.54      inference('split', [status(esa)], ['53'])).
% 0.22/0.54  thf('141', plain,
% 0.22/0.54      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) | 
% 0.22/0.54       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.22/0.54      inference('sup-', [status(thm)], ['139', '140'])).
% 0.22/0.54  thf('142', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['54', '63', '114', '141'])).
% 0.22/0.54  thf('143', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['138', '142'])).
% 0.22/0.54  thf('144', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['137', '143'])).
% 0.22/0.54  thf('145', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('146', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.22/0.54      inference('clc', [status(thm)], ['144', '145'])).
% 0.22/0.54  thf('147', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('148', plain, ((v2_struct_0 @ sk_C)),
% 0.22/0.54      inference('clc', [status(thm)], ['146', '147'])).
% 0.22/0.54  thf('149', plain, ($false), inference('demod', [status(thm)], ['0', '148'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
