%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hz047FV9al

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 465 expanded)
%              Number of leaves         :   31 ( 147 expanded)
%              Depth                    :   21
%              Number of atoms          : 2247 (20689 expanded)
%              Number of equality atoms :   29 ( 264 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v3_pre_topc @ X16 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( X15 != X17 )
      | ~ ( r1_tmap_1 @ X13 @ X18 @ X19 @ X15 )
      | ( r1_tmap_1 @ X14 @ X18 @ ( k2_tmap_1 @ X13 @ X18 @ X19 @ X14 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_tmap_1 @ X14 @ X18 @ ( k2_tmap_1 @ X13 @ X18 @ X19 @ X14 ) @ X17 )
      | ~ ( r1_tmap_1 @ X13 @ X18 @ X19 @ X17 )
      | ~ ( r1_tarski @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v3_pre_topc @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
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
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

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
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','28','33','34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','38'])).

thf('40',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r2_hidden @ sk_H @ sk_F )
        | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['17','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['13','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ( ( k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) @ X12 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
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
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( k2_tmap_1 @ X6 @ X4 @ X7 @ X5 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('72',plain,(
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
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['8'])).

thf('92',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['53','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('103',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['14'])).

thf('104',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v3_pre_topc @ X16 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( X15 != X17 )
      | ~ ( r1_tmap_1 @ X14 @ X18 @ ( k2_tmap_1 @ X13 @ X18 @ X19 @ X14 ) @ X17 )
      | ( r1_tmap_1 @ X13 @ X18 @ X19 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('107',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_tmap_1 @ X13 @ X18 @ X19 @ X17 )
      | ~ ( r1_tmap_1 @ X14 @ X18 @ ( k2_tmap_1 @ X13 @ X18 @ X19 @ X14 ) @ X17 )
      | ~ ( r1_tarski @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v3_pre_topc @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
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
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('110',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('111',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['104','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( r2_hidden @ sk_H @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['101','120'])).

thf('122',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['46','47'])).

thf('124',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['3','12','99','100','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hz047FV9al
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:55 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 65 iterations in 0.025s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(t84_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                         ( v1_funct_2 @
% 0.21/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                         ( m1_subset_1 @
% 0.21/0.50                           E @ 
% 0.21/0.50                           ( k1_zfmisc_1 @
% 0.21/0.50                             ( k2_zfmisc_1 @
% 0.21/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.50                         ( ![F:$i]:
% 0.21/0.50                           ( ( m1_subset_1 @
% 0.21/0.50                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.50                             ( ![G:$i]:
% 0.21/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                                 ( ![H:$i]:
% 0.21/0.50                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.21/0.50                                         ( r2_hidden @ G @ F ) & 
% 0.21/0.50                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.50                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.50                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.50                                         ( r1_tmap_1 @
% 0.21/0.50                                           C @ B @ 
% 0.21/0.50                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.50                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50                ( l1_pre_topc @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                      ( ![E:$i]:
% 0.21/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                            ( v1_funct_2 @
% 0.21/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                            ( m1_subset_1 @
% 0.21/0.50                              E @ 
% 0.21/0.50                              ( k1_zfmisc_1 @
% 0.21/0.50                                ( k2_zfmisc_1 @
% 0.21/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.50                            ( ![F:$i]:
% 0.21/0.50                              ( ( m1_subset_1 @
% 0.21/0.50                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.50                                ( ![G:$i]:
% 0.21/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                                    ( ![H:$i]:
% 0.21/0.50                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.50                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.21/0.50                                            ( r2_hidden @ G @ F ) & 
% 0.21/0.50                                            ( r1_tarski @
% 0.21/0.50                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.50                                            ( ( G ) = ( H ) ) ) =>
% 0.21/0.50                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.50                                            ( r1_tmap_1 @
% 0.21/0.50                                              C @ B @ 
% 0.21/0.50                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.50                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.21/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.50      inference('split', [status(esa)], ['6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('10', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) | 
% 0.21/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.50  thf('13', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.50        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf('16', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t66_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                 ( m1_subset_1 @
% 0.21/0.50                   C @ 
% 0.21/0.50                   ( k1_zfmisc_1 @
% 0.21/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( m1_subset_1 @
% 0.21/0.50                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50                       ( ![F:$i]:
% 0.21/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                           ( ![G:$i]:
% 0.21/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.50                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.21/0.50                                   ( r2_hidden @ F @ E ) & 
% 0.21/0.50                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.50                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.50                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.50                                   ( r1_tmap_1 @
% 0.21/0.50                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X14)
% 0.21/0.50          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (v3_pre_topc @ X16 @ X13)
% 0.21/0.50          | ~ (r2_hidden @ X15 @ X16)
% 0.21/0.50          | ~ (r1_tarski @ X16 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ((X15) != (X17))
% 0.21/0.50          | ~ (r1_tmap_1 @ X13 @ X18 @ X19 @ X15)
% 0.21/0.50          | (r1_tmap_1 @ X14 @ X18 @ (k2_tmap_1 @ X13 @ X18 @ X19 @ X14) @ X17)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))))
% 0.21/0.50          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (v1_funct_1 @ X19)
% 0.21/0.50          | ~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | (v2_struct_0 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | ~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v1_funct_1 @ X19)
% 0.21/0.50          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.21/0.50          | (r1_tmap_1 @ X14 @ X18 @ (k2_tmap_1 @ X13 @ X18 @ X19 @ X14) @ X17)
% 0.21/0.50          | ~ (r1_tmap_1 @ X13 @ X18 @ X19 @ X17)
% 0.21/0.50          | ~ (r1_tarski @ X16 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (r2_hidden @ X17 @ X16)
% 0.21/0.50          | ~ (v3_pre_topc @ X16 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.50          | (v2_struct_0 @ X14)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.50  thf('23', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X1)
% 0.21/0.50          | ~ (v2_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.50  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['22', '28', '33', '34', '35', '36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ sk_F)
% 0.21/0.50          | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '38'])).
% 0.21/0.50  thf('40', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1)
% 0.21/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ sk_F)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_struct_0 @ sk_D)
% 0.21/0.50           | (v2_struct_0 @ X0)
% 0.21/0.50           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.21/0.50           | ~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.50           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.50           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.21/0.50              sk_H)
% 0.21/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.21/0.50           | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '41'])).
% 0.21/0.50  thf('43', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, (((sk_G) = (sk_H))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_struct_0 @ sk_D)
% 0.21/0.50           | (v2_struct_0 @ X0)
% 0.21/0.50           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50           | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.50           | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.21/0.50              sk_H)
% 0.21/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.21/0.50           | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B)
% 0.21/0.50         | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.21/0.50         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.21/0.50         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '49'])).
% 0.21/0.50  thf('51', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B)
% 0.21/0.50         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_H)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.50  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d5_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                         ( v1_funct_2 @
% 0.21/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                         ( m1_subset_1 @
% 0.21/0.50                           E @ 
% 0.21/0.50                           ( k1_zfmisc_1 @
% 0.21/0.50                             ( k2_zfmisc_1 @
% 0.21/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.50                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.50                           ( k2_partfun1 @
% 0.21/0.50                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.50                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X8)
% 0.21/0.50          | ~ (v2_pre_topc @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.50          | ~ (m1_pre_topc @ X9 @ X11)
% 0.21/0.50          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.21/0.50                 X12 @ (u1_struct_0 @ X9)))
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.21/0.50          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.21/0.50          | ~ (v1_funct_1 @ X12)
% 0.21/0.50          | ~ (m1_pre_topc @ X11 @ X10)
% 0.21/0.50          | ~ (l1_pre_topc @ X10)
% 0.21/0.50          | ~ (v2_pre_topc @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '63'])).
% 0.21/0.50  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.50        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '67'])).
% 0.21/0.50  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d4_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                 ( m1_subset_1 @
% 0.21/0.50                   C @ 
% 0.21/0.50                   ( k1_zfmisc_1 @
% 0.21/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.50                     ( k2_partfun1 @
% 0.21/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X4)
% 0.21/0.50          | ~ (v2_pre_topc @ X4)
% 0.21/0.50          | ~ (l1_pre_topc @ X4)
% 0.21/0.50          | ~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.50          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.21/0.50                 (u1_struct_0 @ X5)))
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.21/0.50          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (l1_pre_topc @ X6)
% 0.21/0.50          | ~ (v2_pre_topc @ X6)
% 0.21/0.50          | (v2_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.50  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.21/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.50        | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['69', '79'])).
% 0.21/0.50  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_D)
% 0.21/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.21/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.50  thf('83', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.21/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.50            (u1_struct_0 @ sk_C)))),
% 0.21/0.50      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.50  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.50            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['68', '84', '85'])).
% 0.21/0.50  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.50            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.21/0.50      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.50         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.21/0.50      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.21/0.50           sk_H))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['53', '92'])).
% 0.21/0.50  thf('94', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('clc', [status(thm)], ['93', '94'])).
% 0.21/0.50  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('97', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_C))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.50  thf('98', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.21/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.21/0.50      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('split', [status(esa)], ['6'])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.50         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.21/0.50      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('103', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('split', [status(esa)], ['14'])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 0.21/0.50         sk_H))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['102', '103'])).
% 0.21/0.50  thf('105', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('106', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X14)
% 0.21/0.50          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (v3_pre_topc @ X16 @ X13)
% 0.21/0.50          | ~ (r2_hidden @ X15 @ X16)
% 0.21/0.50          | ~ (r1_tarski @ X16 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ((X15) != (X17))
% 0.21/0.50          | ~ (r1_tmap_1 @ X14 @ X18 @ (k2_tmap_1 @ X13 @ X18 @ X19 @ X14) @ 
% 0.21/0.50               X17)
% 0.21/0.50          | (r1_tmap_1 @ X13 @ X18 @ X19 @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))))
% 0.21/0.50          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (v1_funct_1 @ X19)
% 0.21/0.50          | ~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | (v2_struct_0 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.21/0.50  thf('107', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | ~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v1_funct_1 @ X19)
% 0.21/0.50          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X18))))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.21/0.50          | (r1_tmap_1 @ X13 @ X18 @ X19 @ X17)
% 0.21/0.50          | ~ (r1_tmap_1 @ X14 @ X18 @ (k2_tmap_1 @ X13 @ X18 @ X19 @ X14) @ 
% 0.21/0.50               X17)
% 0.21/0.50          | ~ (r1_tarski @ X16 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (r2_hidden @ X17 @ X16)
% 0.21/0.50          | ~ (v3_pre_topc @ X16 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.50          | (v2_struct_0 @ X14)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('simplify', [status(thm)], ['106'])).
% 0.21/0.50  thf('108', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.21/0.50               X1)
% 0.21/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['105', '107'])).
% 0.21/0.50  thf('109', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.50  thf('110', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('111', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('112', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('114', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('115', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.21/0.50               X1)
% 0.21/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['108', '109', '110', '111', '112', '113', '114'])).
% 0.21/0.50  thf('116', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_struct_0 @ sk_B)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.21/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.21/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.50           | ~ (r2_hidden @ sk_H @ X0)
% 0.21/0.50           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.21/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.21/0.50           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50           | (v2_struct_0 @ sk_C)
% 0.21/0.50           | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['104', '115'])).
% 0.21/0.50  thf('117', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('118', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('120', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_struct_0 @ sk_B)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.21/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.50           | ~ (r2_hidden @ sk_H @ X0)
% 0.21/0.50           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.21/0.50           | (v2_struct_0 @ sk_C)
% 0.21/0.50           | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.21/0.50  thf('121', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.21/0.50         | ~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.50         | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.21/0.50         | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['101', '120'])).
% 0.21/0.50  thf('122', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('123', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('124', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('125', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_D)
% 0.21/0.50         | (v2_struct_0 @ sk_C)
% 0.21/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.21/0.50         | (v2_struct_0 @ sk_B)))
% 0.21/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.21/0.50  thf('126', plain,
% 0.21/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('127', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.50  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('129', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('clc', [status(thm)], ['127', '128'])).
% 0.21/0.50  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('131', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_C))
% 0.21/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)) & 
% 0.21/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.50      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.50  thf('132', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('133', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.21/0.50       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))),
% 0.21/0.50      inference('sup-', [status(thm)], ['131', '132'])).
% 0.21/0.50  thf('134', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['3', '12', '99', '100', '133'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
