%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aNp32Z9FPM

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 799 expanded)
%              Number of leaves         :   35 ( 240 expanded)
%              Depth                    :   27
%              Number of atoms          : 2439 (35386 expanded)
%              Number of equality atoms :   33 ( 458 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( ( k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) @ X25 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k2_tmap_1 @ X19 @ X17 @ X20 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X20 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['15','57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ( X31 != X28 )
      | ~ ( r1_tmap_1 @ X26 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tmap_1 @ X26 @ X29 @ X30 @ X28 )
      | ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('88',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('99',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['62','97','98'])).

thf('100',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['58','99'])).

thf('101',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('103',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r1_tmap_1 @ X38 @ X35 @ ( k3_tmap_1 @ X37 @ X35 @ X36 @ X38 @ X41 ) @ X40 )
      | ( r1_tmap_1 @ X36 @ X35 @ X41 @ X42 )
      | ( X42 != X40 )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X42 @ X39 )
      | ~ ( v3_pre_topc @ X39 @ X36 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('104',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X36 ) )
      | ~ ( v3_pre_topc @ X39 @ X36 )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X38 ) )
      | ( r1_tmap_1 @ X36 @ X35 @ X41 @ X40 )
      | ~ ( r1_tmap_1 @ X38 @ X35 @ ( k3_tmap_1 @ X37 @ X35 @ X36 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_pre_topc @ X38 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

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

thf('125',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ X15 @ X16 )
      | ( X15 != X13 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('126',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v3_pre_topc @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','126'])).

thf('128',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['123','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','132','135','136'])).

thf('138',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['88'])).

thf('139',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('142',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['61'])).

thf('145',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['62','97','145'])).

thf('147',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['140','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['0','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aNp32Z9FPM
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 108 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t85_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                         ( v1_funct_2 @
% 0.20/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                         ( m1_subset_1 @
% 0.20/0.52                           E @ 
% 0.20/0.52                           ( k1_zfmisc_1 @
% 0.20/0.52                             ( k2_zfmisc_1 @
% 0.20/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.52                         ( ![F:$i]:
% 0.20/0.52                           ( ( m1_subset_1 @
% 0.20/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52                             ( ![G:$i]:
% 0.20/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.52                                 ( ![H:$i]:
% 0.20/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.52                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.52                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.52                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.52                                         ( r1_tmap_1 @
% 0.20/0.52                                           C @ A @ 
% 0.20/0.52                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52                ( l1_pre_topc @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.52                      ( ![E:$i]:
% 0.20/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                            ( v1_funct_2 @
% 0.20/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                            ( m1_subset_1 @
% 0.20/0.52                              E @ 
% 0.20/0.52                              ( k1_zfmisc_1 @
% 0.20/0.52                                ( k2_zfmisc_1 @
% 0.20/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.52                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.52                            ( ![F:$i]:
% 0.20/0.52                              ( ( m1_subset_1 @
% 0.20/0.52                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52                                ( ![G:$i]:
% 0.20/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.52                                    ( ![H:$i]:
% 0.20/0.52                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.52                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.52                                            ( r1_tarski @
% 0.20/0.52                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.52                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.52                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.52                                            ( r1_tmap_1 @
% 0.20/0.52                                              C @ A @ 
% 0.20/0.52                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.52                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t39_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.52  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('10', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.52        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('split', [status(esa)], ['14'])).
% 0.20/0.52  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_E @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                         ( v1_funct_2 @
% 0.20/0.52                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                         ( m1_subset_1 @
% 0.20/0.52                           E @ 
% 0.20/0.52                           ( k1_zfmisc_1 @
% 0.20/0.52                             ( k2_zfmisc_1 @
% 0.20/0.52                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.52                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52                           ( k2_partfun1 @
% 0.20/0.52                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.52                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.52          | ~ (m1_pre_topc @ X22 @ X24)
% 0.20/0.52          | ((k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21) @ 
% 0.20/0.52                 X25 @ (u1_struct_0 @ X22)))
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))))
% 0.20/0.52          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))
% 0.20/0.52          | ~ (v1_funct_1 @ X25)
% 0.20/0.52          | ~ (m1_pre_topc @ X24 @ X23)
% 0.20/0.52          | ~ (l1_pre_topc @ X23)
% 0.20/0.52          | ~ (v2_pre_topc @ X23)
% 0.20/0.52          | (v2_struct_0 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.52          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '25'])).
% 0.20/0.52  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '29'])).
% 0.20/0.52  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_E @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d4_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.52                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.52                     ( k2_partfun1 @
% 0.20/0.52                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.52                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X17)
% 0.20/0.52          | ~ (v2_pre_topc @ X17)
% 0.20/0.52          | ~ (l1_pre_topc @ X17)
% 0.20/0.52          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.52          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 0.20/0.53                 X20 @ (u1_struct_0 @ X18)))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 0.20/0.53          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (v1_funct_1 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.53          | (v2_pre_topc @ X6)
% 0.20/0.53          | ~ (l1_pre_topc @ X7)
% 0.20/0.53          | ~ (v2_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_D)
% 0.20/0.53          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['34', '40', '41', '42', '43', '44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.53        | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '46'])).
% 0.20/0.53  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D)
% 0.20/0.53        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '51', '52'])).
% 0.20/0.53  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.53         sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.53      inference('split', [status(esa)], ['61'])).
% 0.20/0.53  thf('63', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t64_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                       ( ![F:$i]:
% 0.20/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.53                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.53                             ( r1_tmap_1 @
% 0.20/0.53                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X27)
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.53          | (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ X28)
% 0.20/0.53          | ((X31) != (X28))
% 0.20/0.53          | ~ (r1_tmap_1 @ X26 @ X29 @ X30 @ X31)
% 0.20/0.53          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.20/0.53          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ~ (l1_pre_topc @ X29)
% 0.20/0.53          | ~ (v2_pre_topc @ X29)
% 0.20/0.53          | (v2_struct_0 @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X29)
% 0.20/0.53          | ~ (v2_pre_topc @ X29)
% 0.20/0.53          | ~ (l1_pre_topc @ X29)
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.20/0.53          | ~ (r1_tmap_1 @ X26 @ X29 @ X30 @ X28)
% 0.20/0.53          | (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ X28)
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.53          | (v2_struct_0 @ X27)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X26))),
% 0.20/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.53  thf('72', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['71', '72', '73', '74', '75', '76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.53              sk_H)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.53           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '78'])).
% 0.20/0.53  thf('80', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.53              sk_H)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.53           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '83'])).
% 0.20/0.53  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.53           sk_H))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['87', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '90'])).
% 0.20/0.53  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('clc', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.53       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('split', [status(esa)], ['66'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['62', '97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.53        sk_H)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['58', '99'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t84_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                         ( v1_funct_2 @
% 0.20/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @
% 0.20/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.53                             ( ![G:$i]:
% 0.20/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                 ( ![H:$i]:
% 0.20/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.53                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.53                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.53                                         ( r1_tmap_1 @
% 0.20/0.53                                           C @ B @ 
% 0.20/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.20/0.53         X42 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X35)
% 0.20/0.53          | ~ (v2_pre_topc @ X35)
% 0.20/0.53          | ~ (l1_pre_topc @ X35)
% 0.20/0.53          | (v2_struct_0 @ X36)
% 0.20/0.53          | ~ (m1_pre_topc @ X36 @ X37)
% 0.20/0.53          | ~ (m1_pre_topc @ X38 @ X36)
% 0.20/0.53          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.20/0.53          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X38))
% 0.20/0.53          | ~ (r1_tmap_1 @ X38 @ X35 @ 
% 0.20/0.53               (k3_tmap_1 @ X37 @ X35 @ X36 @ X38 @ X41) @ X40)
% 0.20/0.53          | (r1_tmap_1 @ X36 @ X35 @ X41 @ X42)
% 0.20/0.53          | ((X42) != (X40))
% 0.20/0.53          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X38))
% 0.20/0.53          | ~ (r2_hidden @ X42 @ X39)
% 0.20/0.53          | ~ (v3_pre_topc @ X39 @ X36)
% 0.20/0.53          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X36))
% 0.20/0.53          | ~ (m1_subset_1 @ X41 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))))
% 0.20/0.53          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))
% 0.20/0.53          | ~ (v1_funct_1 @ X41)
% 0.20/0.53          | ~ (m1_pre_topc @ X38 @ X37)
% 0.20/0.53          | (v2_struct_0 @ X38)
% 0.20/0.53          | ~ (l1_pre_topc @ X37)
% 0.20/0.53          | ~ (v2_pre_topc @ X37)
% 0.20/0.53          | (v2_struct_0 @ X37))),
% 0.20/0.53      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X37)
% 0.20/0.53          | ~ (v2_pre_topc @ X37)
% 0.20/0.53          | ~ (l1_pre_topc @ X37)
% 0.20/0.53          | (v2_struct_0 @ X38)
% 0.20/0.53          | ~ (m1_pre_topc @ X38 @ X37)
% 0.20/0.53          | ~ (v1_funct_1 @ X41)
% 0.20/0.53          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))
% 0.20/0.53          | ~ (m1_subset_1 @ X41 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))))
% 0.20/0.53          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X36))
% 0.20/0.53          | ~ (v3_pre_topc @ X39 @ X36)
% 0.20/0.53          | ~ (r2_hidden @ X40 @ X39)
% 0.20/0.53          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X38))
% 0.20/0.53          | (r1_tmap_1 @ X36 @ X35 @ X41 @ X40)
% 0.20/0.53          | ~ (r1_tmap_1 @ X38 @ X35 @ 
% 0.20/0.53               (k3_tmap_1 @ X37 @ X35 @ X36 @ X38 @ X41) @ X40)
% 0.20/0.53          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X38))
% 0.20/0.53          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.20/0.53          | ~ (m1_pre_topc @ X38 @ X36)
% 0.20/0.53          | ~ (m1_pre_topc @ X36 @ X37)
% 0.20/0.53          | (v2_struct_0 @ X36)
% 0.20/0.53          | ~ (l1_pre_topc @ X35)
% 0.20/0.53          | ~ (v2_pre_topc @ X35)
% 0.20/0.53          | (v2_struct_0 @ X35))),
% 0.20/0.53      inference('simplify', [status(thm)], ['103'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['102', '104'])).
% 0.20/0.53  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('109', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_C)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '110'])).
% 0.20/0.53  thf('112', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('115', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('116', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('117', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_C)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['111', '112', '113', '114', '115', '116'])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (v2_struct_0 @ sk_C)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['100', '117'])).
% 0.20/0.53  thf('119', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('120', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('121', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_C)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_C)
% 0.20/0.53        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.53        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.53        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '121'])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.53  thf(t33_tops_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.53                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('125', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.53          | ~ (v3_pre_topc @ X13 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.53          | (v3_pre_topc @ X15 @ X16)
% 0.20/0.53          | ((X15) != (X13))
% 0.20/0.53          | ~ (m1_pre_topc @ X16 @ X14)
% 0.20/0.53          | ~ (l1_pre_topc @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X14)
% 0.20/0.53          | ~ (m1_pre_topc @ X16 @ X14)
% 0.20/0.53          | (v3_pre_topc @ X13 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.53          | ~ (v3_pre_topc @ X13 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['125'])).
% 0.20/0.53  thf('127', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.20/0.53          | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['124', '126'])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.53        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53        | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.53        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['123', '127'])).
% 0.20/0.53  thf('129', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('130', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('131', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('132', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.20/0.53  thf('133', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('134', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('135', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.53      inference('demod', [status(thm)], ['133', '134'])).
% 0.20/0.53  thf('136', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('137', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_C)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['122', '132', '135', '136'])).
% 0.20/0.53  thf('138', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['88'])).
% 0.20/0.53  thf('139', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('140', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['138', '139'])).
% 0.20/0.53  thf('141', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('142', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('143', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['141', '142'])).
% 0.20/0.53  thf('144', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['61'])).
% 0.20/0.53  thf('145', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('sup-', [status(thm)], ['143', '144'])).
% 0.20/0.53  thf('146', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['62', '97', '145'])).
% 0.20/0.53  thf('147', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['140', '146'])).
% 0.20/0.53  thf('148', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_C)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['137', '147'])).
% 0.20/0.53  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('150', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['148', '149'])).
% 0.20/0.53  thf('151', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('152', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['150', '151'])).
% 0.20/0.53  thf('153', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('154', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('clc', [status(thm)], ['152', '153'])).
% 0.20/0.53  thf('155', plain, ($false), inference('demod', [status(thm)], ['0', '154'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
