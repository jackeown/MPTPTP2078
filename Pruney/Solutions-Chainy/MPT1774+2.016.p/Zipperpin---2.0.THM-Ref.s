%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqMRRmDu9Q

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:19 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 424 expanded)
%              Number of leaves         :   31 ( 130 expanded)
%              Depth                    :   26
%              Number of atoms          : 2053 (18064 expanded)
%              Number of equality atoms :   16 ( 206 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X17 )
      | ( X17 != X20 )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['21','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['20','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['24'])).

thf('60',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['19','58','59'])).

thf('61',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['15','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X28 )
      | ( X28 != X26 )
      | ~ ( r1_tarski @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X28 @ X25 )
      | ~ ( v3_pre_topc @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v3_pre_topc @ X25 @ X22 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( r1_tarski @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('76',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','79'])).

thf('81',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('86',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( ( v3_pre_topc @ C @ A )
                          & ( r1_tarski @ C @ ( u1_struct_0 @ B ) )
                          & ( r1_tarski @ D @ C )
                          & ( D = E ) )
                       => ( ( v3_pre_topc @ E @ B )
                        <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tarski @ X31 @ X32 )
      | ( X31 != X33 )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( v3_pre_topc @ X33 @ X29 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t9_tsep_1])).

thf('89',plain,(
    ! [X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ X33 @ X29 )
      | ~ ( v3_pre_topc @ X33 @ X30 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ~ ( r1_tarski @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_pre_topc @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ sk_F @ sk_B )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_B )
      | ~ ( r1_tarski @ sk_F @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','94'])).

thf('96',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','98'])).

thf('100',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( v3_pre_topc @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['85','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('103',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['100','101','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','84','105'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['48'])).

thf('108',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('111',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['18'])).

thf('114',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['19','58','114'])).

thf('116',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['109','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqMRRmDu9Q
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 146 iterations in 0.093s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_H_type, type, sk_H: $i).
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.59  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.39/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.59  thf(t85_tmap_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                         ( v1_funct_2 @
% 0.39/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.59                         ( m1_subset_1 @
% 0.39/0.59                           E @ 
% 0.39/0.59                           ( k1_zfmisc_1 @
% 0.39/0.59                             ( k2_zfmisc_1 @
% 0.39/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.39/0.59                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.59                         ( ![F:$i]:
% 0.39/0.59                           ( ( m1_subset_1 @
% 0.39/0.59                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.59                             ( ![G:$i]:
% 0.39/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                                 ( ![H:$i]:
% 0.39/0.59                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.39/0.59                                         ( r2_hidden @ G @ F ) & 
% 0.39/0.59                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.59                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.59                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.39/0.59                                         ( r1_tmap_1 @
% 0.39/0.59                                           C @ A @ 
% 0.39/0.59                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.39/0.59                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.59            ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59                ( l1_pre_topc @ B ) ) =>
% 0.39/0.59              ( ![C:$i]:
% 0.39/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.39/0.59                  ( ![D:$i]:
% 0.39/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.39/0.59                      ( ![E:$i]:
% 0.39/0.59                        ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                            ( v1_funct_2 @
% 0.39/0.59                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.59                            ( m1_subset_1 @
% 0.39/0.59                              E @ 
% 0.39/0.59                              ( k1_zfmisc_1 @
% 0.39/0.59                                ( k2_zfmisc_1 @
% 0.39/0.59                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.39/0.59                          ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.59                            ( ![F:$i]:
% 0.39/0.59                              ( ( m1_subset_1 @
% 0.39/0.59                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.59                                ( ![G:$i]:
% 0.39/0.59                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                                    ( ![H:$i]:
% 0.39/0.59                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.39/0.59                                            ( r2_hidden @ G @ F ) & 
% 0.39/0.59                                            ( r1_tarski @
% 0.39/0.59                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.59                                            ( ( G ) = ( H ) ) ) =>
% 0.39/0.59                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.39/0.59                                            ( r1_tmap_1 @
% 0.39/0.59                                              C @ A @ 
% 0.39/0.59                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.39/0.59                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.39/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t3_subset, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X3 : $i, X5 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf(t39_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.59               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X8 @ X9)
% 0.39/0.59          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.59          | ~ (l1_pre_topc @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ X0)
% 0.39/0.59          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.39/0.59        | ~ (l1_pre_topc @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '6'])).
% 0.39/0.59  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_m1_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.59  thf('10', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('12', plain, ((l1_pre_topc @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.59      inference('split', [status(esa)], ['14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('17', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.39/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.39/0.59       ~
% 0.39/0.59       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.59      inference('split', [status(esa)], ['18'])).
% 0.39/0.59  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('21', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('23', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.39/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('split', [status(esa)], ['24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_E @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t81_tmap_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                         ( v1_funct_2 @
% 0.39/0.59                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                         ( m1_subset_1 @
% 0.39/0.59                           E @ 
% 0.39/0.59                           ( k1_zfmisc_1 @
% 0.39/0.59                             ( k2_zfmisc_1 @
% 0.39/0.59                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                       ( ![F:$i]:
% 0.39/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                           ( ![G:$i]:
% 0.39/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                               ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.59                                   ( m1_pre_topc @ D @ C ) & 
% 0.39/0.59                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.39/0.59                                 ( r1_tmap_1 @
% 0.39/0.59                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.39/0.59                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X14)
% 0.39/0.59          | ~ (v2_pre_topc @ X14)
% 0.39/0.59          | ~ (l1_pre_topc @ X14)
% 0.39/0.59          | (v2_struct_0 @ X15)
% 0.39/0.59          | ~ (m1_pre_topc @ X15 @ X16)
% 0.39/0.59          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.39/0.59          | ~ (m1_pre_topc @ X15 @ X18)
% 0.39/0.59          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X17)
% 0.39/0.59          | ((X17) != (X20))
% 0.39/0.59          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.39/0.59             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.39/0.59          | ~ (m1_subset_1 @ X19 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.39/0.59          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.39/0.59          | ~ (v1_funct_1 @ X19)
% 0.39/0.59          | ~ (m1_pre_topc @ X18 @ X16)
% 0.39/0.59          | (v2_struct_0 @ X18)
% 0.39/0.59          | ~ (l1_pre_topc @ X16)
% 0.39/0.59          | ~ (v2_pre_topc @ X16)
% 0.39/0.59          | (v2_struct_0 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X16)
% 0.39/0.59          | ~ (v2_pre_topc @ X16)
% 0.39/0.59          | ~ (l1_pre_topc @ X16)
% 0.39/0.59          | (v2_struct_0 @ X18)
% 0.39/0.59          | ~ (m1_pre_topc @ X18 @ X16)
% 0.39/0.59          | ~ (v1_funct_1 @ X19)
% 0.39/0.59          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.39/0.59          | ~ (m1_subset_1 @ X19 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.39/0.59          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.39/0.59             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.39/0.59          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X20)
% 0.39/0.59          | ~ (m1_pre_topc @ X15 @ X18)
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.39/0.59          | ~ (m1_pre_topc @ X15 @ X16)
% 0.39/0.59          | (v2_struct_0 @ X15)
% 0.39/0.59          | ~ (l1_pre_topc @ X14)
% 0.39/0.59          | ~ (v2_pre_topc @ X14)
% 0.39/0.59          | (v2_struct_0 @ X14))),
% 0.39/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ X0)
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.59          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.39/0.59          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.39/0.59             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.39/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.59          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | ~ (l1_pre_topc @ X1)
% 0.39/0.59          | ~ (v2_pre_topc @ X1)
% 0.39/0.59          | (v2_struct_0 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '28'])).
% 0.39/0.59  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ X0)
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.39/0.59          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.39/0.59          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.39/0.59             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | ~ (l1_pre_topc @ X1)
% 0.39/0.59          | ~ (v2_pre_topc @ X1)
% 0.39/0.59          | (v2_struct_0 @ X1))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((![X0 : $i, X1 : $i]:
% 0.39/0.59          ((v2_struct_0 @ X0)
% 0.39/0.59           | ~ (v2_pre_topc @ X0)
% 0.39/0.59           | ~ (l1_pre_topc @ X0)
% 0.39/0.59           | (v2_struct_0 @ sk_D)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.59           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.39/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.39/0.59           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.39/0.59           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.59           | (v2_struct_0 @ X1)
% 0.39/0.59           | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '34'])).
% 0.39/0.59  thf('36', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('38', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      ((![X0 : $i, X1 : $i]:
% 0.39/0.59          ((v2_struct_0 @ X0)
% 0.39/0.59           | ~ (v2_pre_topc @ X0)
% 0.39/0.59           | ~ (l1_pre_topc @ X0)
% 0.39/0.59           | (v2_struct_0 @ sk_D)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.59           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.39/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.39/0.59           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.59           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.59           | (v2_struct_0 @ X1)
% 0.39/0.59           | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((v2_struct_0 @ sk_A)
% 0.39/0.59           | (v2_struct_0 @ sk_C)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.39/0.59           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59           | (v2_struct_0 @ sk_D)
% 0.39/0.59           | ~ (l1_pre_topc @ X0)
% 0.39/0.59           | ~ (v2_pre_topc @ X0)
% 0.39/0.59           | (v2_struct_0 @ X0)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '39'])).
% 0.39/0.59  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((v2_struct_0 @ sk_A)
% 0.39/0.59           | (v2_struct_0 @ sk_C)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.59           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59           | (v2_struct_0 @ sk_D)
% 0.39/0.59           | ~ (l1_pre_topc @ X0)
% 0.39/0.59           | ~ (v2_pre_topc @ X0)
% 0.39/0.59           | (v2_struct_0 @ X0)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_B)
% 0.39/0.59         | ~ (v2_pre_topc @ sk_B)
% 0.39/0.59         | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59         | (v2_struct_0 @ sk_D)
% 0.39/0.59         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.39/0.59         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59         | (v2_struct_0 @ sk_C)
% 0.39/0.59         | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['20', '42'])).
% 0.39/0.59  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_B)
% 0.39/0.59         | (v2_struct_0 @ sk_D)
% 0.39/0.59         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59         | (v2_struct_0 @ sk_C)
% 0.39/0.59         | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.39/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.59      inference('split', [status(esa)], ['48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_A)
% 0.39/0.59         | (v2_struct_0 @ sk_C)
% 0.39/0.59         | (v2_struct_0 @ sk_D)
% 0.39/0.59         | (v2_struct_0 @ sk_B)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['47', '49'])).
% 0.39/0.59  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.59  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('clc', [status(thm)], ['52', '53'])).
% 0.39/0.59  thf('55', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_D))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('clc', [status(thm)], ['54', '55'])).
% 0.39/0.59  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.59       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.39/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.59       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.39/0.59      inference('split', [status(esa)], ['24'])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['19', '58', '59'])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.39/0.59        (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['15', '60'])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_E @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t84_tmap_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.59                         ( v1_funct_2 @
% 0.39/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                         ( m1_subset_1 @
% 0.39/0.59                           E @ 
% 0.39/0.59                           ( k1_zfmisc_1 @
% 0.39/0.59                             ( k2_zfmisc_1 @
% 0.39/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.59                         ( ![F:$i]:
% 0.39/0.59                           ( ( m1_subset_1 @
% 0.39/0.59                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.59                             ( ![G:$i]:
% 0.39/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.59                                 ( ![H:$i]:
% 0.39/0.59                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.59                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.39/0.59                                         ( r2_hidden @ G @ F ) & 
% 0.39/0.59                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.59                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.59                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.59                                         ( r1_tmap_1 @
% 0.39/0.59                                           C @ B @ 
% 0.39/0.59                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.59                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('63', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 0.39/0.59         X28 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X21)
% 0.39/0.59          | ~ (v2_pre_topc @ X21)
% 0.39/0.59          | ~ (l1_pre_topc @ X21)
% 0.39/0.59          | (v2_struct_0 @ X22)
% 0.39/0.59          | ~ (m1_pre_topc @ X22 @ X23)
% 0.39/0.59          | ~ (m1_pre_topc @ X24 @ X22)
% 0.39/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.39/0.59          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.39/0.59          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.39/0.59               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.39/0.59          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X28)
% 0.39/0.59          | ((X28) != (X26))
% 0.39/0.59          | ~ (r1_tarski @ X25 @ (u1_struct_0 @ X24))
% 0.39/0.59          | ~ (r2_hidden @ X28 @ X25)
% 0.39/0.59          | ~ (v3_pre_topc @ X25 @ X22)
% 0.39/0.59          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X22))
% 0.39/0.59          | ~ (m1_subset_1 @ X27 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.39/0.59          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.39/0.59          | ~ (v1_funct_1 @ X27)
% 0.39/0.59          | ~ (m1_pre_topc @ X24 @ X23)
% 0.39/0.59          | (v2_struct_0 @ X24)
% 0.39/0.59          | ~ (l1_pre_topc @ X23)
% 0.39/0.59          | ~ (v2_pre_topc @ X23)
% 0.39/0.59          | (v2_struct_0 @ X23))),
% 0.39/0.59      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X23)
% 0.39/0.59          | ~ (v2_pre_topc @ X23)
% 0.39/0.59          | ~ (l1_pre_topc @ X23)
% 0.39/0.59          | (v2_struct_0 @ X24)
% 0.39/0.59          | ~ (m1_pre_topc @ X24 @ X23)
% 0.39/0.59          | ~ (v1_funct_1 @ X27)
% 0.39/0.59          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.39/0.59          | ~ (m1_subset_1 @ X27 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.39/0.59          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X22))
% 0.39/0.59          | ~ (v3_pre_topc @ X25 @ X22)
% 0.39/0.59          | ~ (r2_hidden @ X26 @ X25)
% 0.39/0.59          | ~ (r1_tarski @ X25 @ (u1_struct_0 @ X24))
% 0.39/0.59          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X26)
% 0.39/0.59          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.39/0.59               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.39/0.59          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.39/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.39/0.59          | ~ (m1_pre_topc @ X24 @ X22)
% 0.39/0.59          | ~ (m1_pre_topc @ X22 @ X23)
% 0.39/0.59          | (v2_struct_0 @ X22)
% 0.39/0.59          | ~ (l1_pre_topc @ X21)
% 0.39/0.59          | ~ (v2_pre_topc @ X21)
% 0.39/0.59          | (v2_struct_0 @ X21))),
% 0.39/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.39/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.59          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.39/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.39/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.39/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.39/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.39/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.39/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (v2_pre_topc @ X0)
% 0.39/0.59          | (v2_struct_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['62', '64'])).
% 0.39/0.59  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.39/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.59          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.39/0.59               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.39/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.39/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.39/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.39/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.39/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (v2_pre_topc @ X0)
% 0.39/0.59          | (v2_struct_0 @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59          | (v2_struct_0 @ sk_C)
% 0.39/0.59          | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.39/0.59          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.39/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.39/0.59          | ~ (r2_hidden @ sk_H @ X0)
% 0.39/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.39/0.59          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.39/0.59          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.39/0.59          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['61', '70'])).
% 0.39/0.59  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('75', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.59  thf('76', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('78', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('79', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B)
% 0.39/0.59          | (v2_struct_0 @ sk_C)
% 0.39/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.39/0.59          | ~ (r2_hidden @ sk_H @ X0)
% 0.39/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.39/0.59          | (v2_struct_0 @ sk_D)
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)],
% 0.39/0.59                ['71', '72', '73', '74', '75', '76', '77', '78'])).
% 0.39/0.59  thf('80', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | (v2_struct_0 @ sk_D)
% 0.39/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.39/0.59        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.59        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.39/0.59        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.39/0.59        | (v2_struct_0 @ sk_C)
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['13', '79'])).
% 0.39/0.59  thf('81', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('82', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('83', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('84', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.39/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.39/0.59  thf('85', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '12'])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('87', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t9_tsep_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59                   ( ![E:$i]:
% 0.39/0.59                     ( ( m1_subset_1 @
% 0.39/0.59                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.59                       ( ( ( v3_pre_topc @ C @ A ) & 
% 0.39/0.59                           ( r1_tarski @ C @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                           ( r1_tarski @ D @ C ) & ( ( D ) = ( E ) ) ) =>
% 0.39/0.59                         ( ( v3_pre_topc @ E @ B ) <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X29 @ X30)
% 0.39/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.39/0.59          | ~ (v3_pre_topc @ X32 @ X30)
% 0.39/0.59          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X29))
% 0.39/0.59          | ~ (r1_tarski @ X31 @ X32)
% 0.39/0.59          | ((X31) != (X33))
% 0.39/0.59          | ~ (v3_pre_topc @ X31 @ X30)
% 0.39/0.59          | (v3_pre_topc @ X33 @ X29)
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.39/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.39/0.59          | ~ (l1_pre_topc @ X30)
% 0.39/0.59          | ~ (v2_pre_topc @ X30))),
% 0.39/0.59      inference('cnf', [status(esa)], [t9_tsep_1])).
% 0.39/0.59  thf('89', plain,
% 0.39/0.59      (![X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.39/0.59         (~ (v2_pre_topc @ X30)
% 0.39/0.59          | ~ (l1_pre_topc @ X30)
% 0.39/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.39/0.59          | (v3_pre_topc @ X33 @ X29)
% 0.39/0.59          | ~ (v3_pre_topc @ X33 @ X30)
% 0.39/0.59          | ~ (r1_tarski @ X33 @ X32)
% 0.39/0.59          | ~ (r1_tarski @ X32 @ (u1_struct_0 @ X29))
% 0.39/0.59          | ~ (v3_pre_topc @ X32 @ X30)
% 0.39/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.39/0.59          | ~ (m1_pre_topc @ X29 @ X30))),
% 0.39/0.59      inference('simplify', [status(thm)], ['88'])).
% 0.39/0.59  thf('90', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.39/0.59          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.39/0.59          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (r1_tarski @ X1 @ sk_F)
% 0.39/0.59          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.39/0.59          | (v3_pre_topc @ X1 @ X0)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['87', '89'])).
% 0.39/0.59  thf('91', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('94', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.39/0.59          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (r1_tarski @ X1 @ sk_F)
% 0.39/0.59          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.39/0.59          | (v3_pre_topc @ X1 @ X0)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.59      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.39/0.59  thf('95', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | (v3_pre_topc @ sk_F @ X0)
% 0.39/0.59          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.39/0.59          | ~ (r1_tarski @ sk_F @ sk_F)
% 0.39/0.59          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['86', '94'])).
% 0.39/0.59  thf('96', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('97', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('98', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['97'])).
% 0.39/0.59  thf('99', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | (v3_pre_topc @ sk_F @ X0)
% 0.39/0.59          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['95', '96', '98'])).
% 0.39/0.59  thf('100', plain,
% 0.39/0.59      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.39/0.59        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.39/0.59        | (v3_pre_topc @ sk_F @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['85', '99'])).
% 0.39/0.59  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('102', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.39/0.59      inference('demod', [status(thm)], ['7', '12'])).
% 0.39/0.59  thf('103', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('104', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.59  thf('105', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['100', '101', '104'])).
% 0.39/0.59  thf('106', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | (v2_struct_0 @ sk_D)
% 0.39/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.39/0.59        | (v2_struct_0 @ sk_C)
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['80', '81', '84', '105'])).
% 0.39/0.59  thf('107', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.39/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.39/0.59      inference('split', [status(esa)], ['48'])).
% 0.39/0.59  thf('108', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('109', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.39/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.39/0.59      inference('demod', [status(thm)], ['107', '108'])).
% 0.39/0.59  thf('110', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.39/0.59      inference('split', [status(esa)], ['14'])).
% 0.39/0.59  thf('111', plain, (((sk_G) = (sk_H))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('112', plain,
% 0.39/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.39/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.39/0.59      inference('demod', [status(thm)], ['110', '111'])).
% 0.39/0.59  thf('113', plain,
% 0.39/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.39/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.39/0.59      inference('split', [status(esa)], ['18'])).
% 0.39/0.59  thf('114', plain,
% 0.39/0.59      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.39/0.59       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.39/0.59      inference('sup-', [status(thm)], ['112', '113'])).
% 0.39/0.59  thf('115', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['19', '58', '114'])).
% 0.39/0.59  thf('116', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['109', '115'])).
% 0.39/0.59  thf('117', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | (v2_struct_0 @ sk_C)
% 0.39/0.59        | (v2_struct_0 @ sk_D)
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['106', '116'])).
% 0.39/0.59  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('119', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.39/0.59  thf('120', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('121', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.39/0.59      inference('clc', [status(thm)], ['119', '120'])).
% 0.39/0.59  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('123', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.59      inference('clc', [status(thm)], ['121', '122'])).
% 0.39/0.59  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
