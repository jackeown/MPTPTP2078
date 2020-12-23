%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.De7gxL5Mjq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 829 expanded)
%              Number of leaves         :   34 ( 250 expanded)
%              Depth                    :   30
%              Number of atoms          : 2289 (35128 expanded)
%              Number of equality atoms :   29 ( 438 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

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
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( ( k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X22 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k2_tmap_1 @ X16 @ X14 @ X17 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X17 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','45','46','47','48','49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tmap_1,axiom,(
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
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X24 ) )
      | ( X25 != X27 )
      | ~ ( r1_tmap_1 @ X24 @ X28 @ ( k2_tmap_1 @ X23 @ X28 @ X29 @ X24 ) @ X27 )
      | ( r1_tmap_1 @ X23 @ X28 @ X29 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('67',plain,(
    ! [X23: $i,X24: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X23 @ X28 @ X29 @ X27 )
      | ~ ( r1_tmap_1 @ X24 @ X28 @ ( k2_tmap_1 @ X23 @ X28 @ X29 @ X24 ) @ X27 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('70',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['76','77','80','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( r2_hidden @ sk_H @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['20','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','19'])).

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

thf('86',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('87',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v3_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['83','93','96','97'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('100',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('110',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ),
    inference('sat_resolution*',[status(thm)],['7','108','109'])).

thf('111',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ),
    inference(simpl_trail,[status(thm)],['5','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X24 ) )
      | ( X25 != X27 )
      | ~ ( r1_tmap_1 @ X23 @ X28 @ X29 @ X25 )
      | ( r1_tmap_1 @ X24 @ X28 @ ( k2_tmap_1 @ X23 @ X28 @ X29 @ X24 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('115',plain,(
    ! [X23: $i,X24: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ X28 @ ( k2_tmap_1 @ X23 @ X28 @ X29 @ X24 ) @ X27 )
      | ~ ( r1_tmap_1 @ X23 @ X28 @ X29 @ X27 )
      | ~ ( r1_tarski @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_pre_topc @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('118',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','123'])).

thf('125',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_H @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('129',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['94','95'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('136',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('137',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['7','108'])).

thf('139',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['0','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.De7gxL5Mjq
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 92 iterations in 0.050s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(t85_tmap_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                         ( v1_funct_2 @
% 0.22/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                         ( m1_subset_1 @
% 0.22/0.52                           E @ 
% 0.22/0.52                           ( k1_zfmisc_1 @
% 0.22/0.52                             ( k2_zfmisc_1 @
% 0.22/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.52                         ( ![F:$i]:
% 0.22/0.52                           ( ( m1_subset_1 @
% 0.22/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                             ( ![G:$i]:
% 0.22/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                                 ( ![H:$i]:
% 0.22/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.22/0.52                                         ( r2_hidden @ G @ F ) & 
% 0.22/0.52                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.22/0.52                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.22/0.52                                         ( r1_tmap_1 @
% 0.22/0.52                                           C @ A @ 
% 0.22/0.52                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.22/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52                ( l1_pre_topc @ B ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                      ( ![E:$i]:
% 0.22/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                            ( v1_funct_2 @
% 0.22/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                            ( m1_subset_1 @
% 0.22/0.52                              E @ 
% 0.22/0.52                              ( k1_zfmisc_1 @
% 0.22/0.52                                ( k2_zfmisc_1 @
% 0.22/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52                          ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.52                            ( ![F:$i]:
% 0.22/0.52                              ( ( m1_subset_1 @
% 0.22/0.52                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                                ( ![G:$i]:
% 0.22/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                                    ( ![H:$i]:
% 0.22/0.52                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.22/0.52                                            ( r2_hidden @ G @ F ) & 
% 0.22/0.52                                            ( r1_tarski @
% 0.22/0.52                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.52                                            ( ( G ) = ( H ) ) ) =>
% 0.22/0.52                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.22/0.52                                            ( r1_tmap_1 @
% 0.22/0.52                                              C @ A @ 
% 0.22/0.52                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.22/0.52                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.52        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('4', plain, (((sk_G) = (sk_H))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.22/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.22/0.52       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.22/0.52      inference('split', [status(esa)], ['6'])).
% 0.22/0.52  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf(t39_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.52          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.52          | ~ (l1_pre_topc @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52        | ~ (l1_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf('15', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_m1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.52  thf('17', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['14', '19'])).
% 0.22/0.52  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                         ( v1_funct_2 @
% 0.22/0.52                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                         ( m1_subset_1 @
% 0.22/0.52                           E @ 
% 0.22/0.52                           ( k1_zfmisc_1 @
% 0.22/0.52                             ( k2_zfmisc_1 @
% 0.22/0.52                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52                       ( ( m1_pre_topc @ D @ C ) =>
% 0.22/0.52                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.52                           ( k2_partfun1 @
% 0.22/0.52                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.22/0.52                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X18)
% 0.22/0.52          | ~ (v2_pre_topc @ X18)
% 0.22/0.52          | ~ (l1_pre_topc @ X18)
% 0.22/0.52          | ~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.52          | ~ (m1_pre_topc @ X19 @ X21)
% 0.22/0.52          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.22/0.52                 X22 @ (u1_struct_0 @ X19)))
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 0.22/0.52          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 0.22/0.52          | ~ (v1_funct_1 @ X22)
% 0.22/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.22/0.52          | ~ (l1_pre_topc @ X20)
% 0.22/0.52          | ~ (v2_pre_topc @ X20)
% 0.22/0.52          | (v2_struct_0 @ X20))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '30'])).
% 0.22/0.52  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.22/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.52        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '34'])).
% 0.22/0.52  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d4_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.52                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.52                     ( k2_partfun1 @
% 0.22/0.52                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.52                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X14)
% 0.22/0.52          | ~ (v2_pre_topc @ X14)
% 0.22/0.52          | ~ (l1_pre_topc @ X14)
% 0.22/0.52          | ~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.52          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 0.22/0.52                 X17 @ (u1_struct_0 @ X15)))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 0.22/0.52          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 0.22/0.52          | ~ (v1_funct_1 @ X17)
% 0.22/0.52          | ~ (l1_pre_topc @ X16)
% 0.22/0.52          | ~ (v2_pre_topc @ X16)
% 0.22/0.52          | (v2_struct_0 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X3 @ X4)
% 0.22/0.52          | (v2_pre_topc @ X3)
% 0.22/0.52          | ~ (l1_pre_topc @ X4)
% 0.22/0.52          | ~ (v2_pre_topc @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('45', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.52  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['39', '45', '46', '47', '48', '49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.22/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.52        | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '51'])).
% 0.22/0.52  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_D)
% 0.22/0.52        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.22/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.22/0.52      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.22/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.22/0.52            (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('57', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.22/0.52            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['35', '56', '57'])).
% 0.22/0.52  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.22/0.52            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.22/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.22/0.52         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.22/0.52         sk_H))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t66_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( m1_subset_1 @
% 0.22/0.52                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.52                       ( ![F:$i]:
% 0.22/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                           ( ![G:$i]:
% 0.22/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.52                                   ( r2_hidden @ F @ E ) & 
% 0.22/0.52                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.52                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.52                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.52                                   ( r1_tmap_1 @
% 0.22/0.52                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X23)
% 0.22/0.52          | ~ (v2_pre_topc @ X23)
% 0.22/0.52          | ~ (l1_pre_topc @ X23)
% 0.22/0.52          | (v2_struct_0 @ X24)
% 0.22/0.52          | ~ (m1_pre_topc @ X24 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (v3_pre_topc @ X26 @ X23)
% 0.22/0.52          | ~ (r2_hidden @ X25 @ X26)
% 0.22/0.52          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ((X25) != (X27))
% 0.22/0.52          | ~ (r1_tmap_1 @ X24 @ X28 @ (k2_tmap_1 @ X23 @ X28 @ X29 @ X24) @ 
% 0.22/0.52               X27)
% 0.22/0.52          | (r1_tmap_1 @ X23 @ X28 @ X29 @ X25)
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.52          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))))
% 0.22/0.52          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))
% 0.22/0.52          | ~ (v1_funct_1 @ X29)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | (v2_struct_0 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | ~ (v1_funct_1 @ X29)
% 0.22/0.52          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))
% 0.22/0.52          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.22/0.52          | (r1_tmap_1 @ X23 @ X28 @ X29 @ X27)
% 0.22/0.52          | ~ (r1_tmap_1 @ X24 @ X28 @ (k2_tmap_1 @ X23 @ X28 @ X29 @ X24) @ 
% 0.22/0.52               X27)
% 0.22/0.52          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ~ (r2_hidden @ X27 @ X26)
% 0.22/0.52          | ~ (v3_pre_topc @ X26 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (m1_pre_topc @ X24 @ X23)
% 0.22/0.52          | (v2_struct_0 @ X24)
% 0.22/0.52          | ~ (l1_pre_topc @ X23)
% 0.22/0.52          | ~ (v2_pre_topc @ X23)
% 0.22/0.52          | (v2_struct_0 @ X23))),
% 0.22/0.52      inference('simplify', [status(thm)], ['66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52               X1)
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['65', '67'])).
% 0.22/0.52  thf('69', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.52  thf('70', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52               X1)
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['68', '69', '70', '71', '72', '73', '74'])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v2_struct_0 @ sk_A)
% 0.22/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.22/0.52           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.22/0.52           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52           | ~ (r2_hidden @ sk_H @ X0)
% 0.22/0.52           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.52           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.22/0.52           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52           | (v2_struct_0 @ sk_C)
% 0.22/0.52           | (v2_struct_0 @ sk_D)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '75'])).
% 0.22/0.52  thf('77', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('78', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('79', plain, (((sk_G) = (sk_H))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('80', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.52  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v2_struct_0 @ sk_A)
% 0.22/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.22/0.52           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52           | ~ (r2_hidden @ sk_H @ X0)
% 0.22/0.52           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.52           | (v2_struct_0 @ sk_C)
% 0.22/0.52           | (v2_struct_0 @ sk_D)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('demod', [status(thm)], ['76', '77', '80', '81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_D)
% 0.22/0.52         | (v2_struct_0 @ sk_C)
% 0.22/0.52         | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.22/0.52         | ~ (r2_hidden @ sk_H @ sk_F)
% 0.22/0.52         | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.22/0.52         | (v2_struct_0 @ sk_A)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '82'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['14', '19'])).
% 0.22/0.52  thf(t33_tops_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.52               ( ( v3_pre_topc @ B @ A ) =>
% 0.22/0.52                 ( ![D:$i]:
% 0.22/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.22/0.52                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.52          | ~ (v3_pre_topc @ X10 @ X11)
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.52          | (v3_pre_topc @ X12 @ X13)
% 0.22/0.52          | ((X12) != (X10))
% 0.22/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.22/0.52          | ~ (l1_pre_topc @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X11)
% 0.22/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.22/0.52          | (v3_pre_topc @ X10 @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.52          | ~ (v3_pre_topc @ X10 @ X11)
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['86'])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.22/0.52          | (v3_pre_topc @ sk_F @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '87'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.52        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.52        | (v3_pre_topc @ sk_F @ sk_D)
% 0.22/0.52        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['84', '88'])).
% 0.22/0.52  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('91', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('92', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('93', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.22/0.52  thf('94', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('95', plain, (((sk_G) = (sk_H))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('96', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.22/0.52      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.52  thf('97', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('98', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_D)
% 0.22/0.52         | (v2_struct_0 @ sk_C)
% 0.22/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.22/0.52         | (v2_struct_0 @ sk_A)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('demod', [status(thm)], ['83', '93', '96', '97'])).
% 0.22/0.52  thf('99', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['6'])).
% 0.22/0.52  thf('100', plain, (((sk_G) = (sk_H))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('101', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.52  thf('102', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['98', '101'])).
% 0.22/0.52  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.52  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('106', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('clc', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf('107', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('108', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.22/0.52       ~
% 0.22/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.22/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.52  thf('109', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.22/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('110', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['7', '108', '109'])).
% 0.22/0.52  thf('111', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['5', '110'])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['14', '19'])).
% 0.22/0.52  thf('113', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('114', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X23)
% 0.22/0.52          | ~ (v2_pre_topc @ X23)
% 0.22/0.52          | ~ (l1_pre_topc @ X23)
% 0.22/0.52          | (v2_struct_0 @ X24)
% 0.22/0.52          | ~ (m1_pre_topc @ X24 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (v3_pre_topc @ X26 @ X23)
% 0.22/0.52          | ~ (r2_hidden @ X25 @ X26)
% 0.22/0.52          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ((X25) != (X27))
% 0.22/0.52          | ~ (r1_tmap_1 @ X23 @ X28 @ X29 @ X25)
% 0.22/0.52          | (r1_tmap_1 @ X24 @ X28 @ (k2_tmap_1 @ X23 @ X28 @ X29 @ X24) @ X27)
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.52          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))))
% 0.22/0.52          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))
% 0.22/0.52          | ~ (v1_funct_1 @ X29)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | (v2_struct_0 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.22/0.52  thf('115', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | ~ (v1_funct_1 @ X29)
% 0.22/0.52          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))
% 0.22/0.52          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X28))))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.22/0.52          | (r1_tmap_1 @ X24 @ X28 @ (k2_tmap_1 @ X23 @ X28 @ X29 @ X24) @ X27)
% 0.22/0.52          | ~ (r1_tmap_1 @ X23 @ X28 @ X29 @ X27)
% 0.22/0.52          | ~ (r1_tarski @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ~ (r2_hidden @ X27 @ X26)
% 0.22/0.52          | ~ (v3_pre_topc @ X26 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (m1_pre_topc @ X24 @ X23)
% 0.22/0.52          | (v2_struct_0 @ X24)
% 0.22/0.52          | ~ (l1_pre_topc @ X23)
% 0.22/0.52          | ~ (v2_pre_topc @ X23)
% 0.22/0.52          | (v2_struct_0 @ X23))),
% 0.22/0.52      inference('simplify', [status(thm)], ['114'])).
% 0.22/0.52  thf('116', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['113', '115'])).
% 0.22/0.52  thf('117', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.52  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('119', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('123', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['116', '117', '118', '119', '120', '121', '122'])).
% 0.22/0.52  thf('124', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ sk_F)
% 0.22/0.52          | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['112', '123'])).
% 0.22/0.52  thf('125', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.22/0.52  thf('126', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ sk_F)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['124', '125'])).
% 0.22/0.52  thf('127', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (r2_hidden @ sk_H @ sk_F)
% 0.22/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52             sk_H)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['111', '126'])).
% 0.22/0.52  thf('128', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.52  thf('129', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.22/0.52      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.52  thf('130', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52             sk_H)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.22/0.52  thf('131', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.22/0.52           sk_H)
% 0.22/0.52        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '130'])).
% 0.22/0.52  thf('132', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('133', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('134', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.22/0.52           sk_H)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.22/0.52  thf('135', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('split', [status(esa)], ['6'])).
% 0.22/0.52  thf('136', plain,
% 0.22/0.52      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.22/0.52         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('137', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.22/0.52           sk_H))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.22/0.52      inference('demod', [status(thm)], ['135', '136'])).
% 0.22/0.52  thf('138', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['7', '108'])).
% 0.22/0.52  thf('139', plain,
% 0.22/0.52      (~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.22/0.52          sk_H)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 0.22/0.52  thf('140', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['134', '139'])).
% 0.22/0.52  thf('141', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('142', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['140', '141'])).
% 0.22/0.52  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('144', plain, ((v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('clc', [status(thm)], ['142', '143'])).
% 0.22/0.52  thf('145', plain, ($false), inference('demod', [status(thm)], ['0', '144'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
