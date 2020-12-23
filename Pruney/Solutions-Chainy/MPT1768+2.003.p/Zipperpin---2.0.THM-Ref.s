%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yZ8GukY320

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:08 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  278 (4687 expanded)
%              Number of leaves         :   29 (1360 expanded)
%              Depth                    :   28
%              Number of atoms          : 3842 (194032 expanded)
%              Number of equality atoms :   70 ( 639 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t79_tmap_1,conjecture,(
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
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ D @ C )
                          & ( m1_pre_topc @ E @ D ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) )).

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
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ D @ C )
                            & ( m1_pre_topc @ E @ D ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('7',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','10','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( k2_tmap_1 @ X10 @ X8 @ X11 @ X9 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X11 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('60',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('61',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('78',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('79',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','76','77','78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(demod,[status(thm)],['80','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','116'])).

thf('118',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['102','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('126',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf(t77_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) @ ( k3_tmap_1 @ X24 @ X22 @ X26 @ X23 @ X25 ) @ ( k2_tmap_1 @ X24 @ X22 @ X27 @ X23 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X22 ) @ X25 @ ( k2_tmap_1 @ X24 @ X22 @ X27 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('141',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','142'])).

thf('144',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['1','16'])).

thf('146',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('148',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('155',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('156',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('157',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('158',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('162',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','163'])).

thf('165',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('167',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( k2_tmap_1 @ X10 @ X8 @ X11 @ X9 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X11 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('171',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('177',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','174','179','180','181'])).

thf('183',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('184',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('185',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('186',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186'])).

thf('188',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['165','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['164','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144','202'])).

thf('204',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('206',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['1','16'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['212','213'])).

thf('215',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['214','215'])).

thf('217',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['1','16'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['206','222'])).

thf('224',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157','158'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['224','230'])).

thf('232',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('233',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['223','238'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['203','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,(
    $false ),
    inference(demod,[status(thm)],['0','246'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yZ8GukY320
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 332 iterations in 0.300s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.77  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.77  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.77  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.58/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.77  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.77  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.77  thf(sk_F_type, type, sk_F: $i).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.58/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.77  thf(t79_tmap_1, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.77             ( l1_pre_topc @ B ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.77                   ( ![E:$i]:
% 0.58/0.77                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.58/0.77                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.58/0.77                         ( ![F:$i]:
% 0.58/0.77                           ( ( ( v1_funct_1 @ F ) & 
% 0.58/0.77                               ( v1_funct_2 @
% 0.58/0.77                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                               ( m1_subset_1 @
% 0.58/0.77                                 F @ 
% 0.58/0.77                                 ( k1_zfmisc_1 @
% 0.58/0.77                                   ( k2_zfmisc_1 @
% 0.58/0.77                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                             ( r2_funct_2 @
% 0.58/0.77                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                               ( k3_tmap_1 @
% 0.58/0.77                                 A @ B @ D @ E @ 
% 0.58/0.77                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.58/0.77                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.77            ( l1_pre_topc @ A ) ) =>
% 0.58/0.77          ( ![B:$i]:
% 0.58/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.77                ( l1_pre_topc @ B ) ) =>
% 0.58/0.77              ( ![C:$i]:
% 0.58/0.77                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.77                  ( ![D:$i]:
% 0.58/0.77                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.77                      ( ![E:$i]:
% 0.58/0.77                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.58/0.77                          ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.58/0.77                            ( ![F:$i]:
% 0.58/0.77                              ( ( ( v1_funct_1 @ F ) & 
% 0.58/0.77                                  ( v1_funct_2 @
% 0.58/0.77                                    F @ ( u1_struct_0 @ C ) @ 
% 0.58/0.77                                    ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                                  ( m1_subset_1 @
% 0.58/0.77                                    F @ 
% 0.58/0.77                                    ( k1_zfmisc_1 @
% 0.58/0.77                                      ( k2_zfmisc_1 @
% 0.58/0.77                                        ( u1_struct_0 @ C ) @ 
% 0.58/0.77                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                                ( r2_funct_2 @
% 0.58/0.77                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                                  ( k3_tmap_1 @
% 0.58/0.77                                    A @ B @ D @ E @ 
% 0.58/0.77                                    ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.58/0.77                                  ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t79_tmap_1])).
% 0.58/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t7_tsep_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_pre_topc @ B @ A ) =>
% 0.58/0.77           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X28 @ X29)
% 0.58/0.77          | (m1_pre_topc @ X30 @ X29)
% 0.58/0.77          | ~ (m1_pre_topc @ X30 @ X28)
% 0.58/0.77          | ~ (l1_pre_topc @ X29)
% 0.58/0.77          | ~ (v2_pre_topc @ X29))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v2_pre_topc @ sk_C)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_C)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (m1_pre_topc @ X0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.77  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc1_pre_topc, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X4 @ X5)
% 0.58/0.77          | (v2_pre_topc @ X4)
% 0.58/0.77          | ~ (l1_pre_topc @ X5)
% 0.58/0.77          | ~ (v2_pre_topc @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('10', plain, ((v2_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.58/0.77  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(dt_m1_pre_topc, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.77  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.77  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.58/0.77      inference('demod', [status(thm)], ['4', '10', '15'])).
% 0.58/0.77  thf('17', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '16'])).
% 0.58/0.77  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(dt_k3_tmap_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.77         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.58/0.77         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.58/0.77         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.58/0.77         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77         ( m1_subset_1 @
% 0.58/0.77           E @ 
% 0.58/0.77           ( k1_zfmisc_1 @
% 0.58/0.77             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.58/0.77         ( v1_funct_2 @
% 0.58/0.77           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.58/0.77           ( u1_struct_0 @ B ) ) & 
% 0.58/0.77         ( m1_subset_1 @
% 0.58/0.77           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.58/0.77           ( k1_zfmisc_1 @
% 0.58/0.77             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X17 @ X18)
% 0.58/0.77          | ~ (m1_pre_topc @ X19 @ X18)
% 0.58/0.77          | ~ (l1_pre_topc @ X20)
% 0.58/0.77          | ~ (v2_pre_topc @ X20)
% 0.58/0.77          | (v2_struct_0 @ X20)
% 0.58/0.77          | ~ (l1_pre_topc @ X18)
% 0.58/0.77          | ~ (v2_pre_topc @ X18)
% 0.58/0.77          | (v2_struct_0 @ X18)
% 0.58/0.77          | ~ (v1_funct_1 @ X21)
% 0.58/0.77          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.58/0.77          | ~ (m1_subset_1 @ X21 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.58/0.77          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.58/0.77             (k1_zfmisc_1 @ 
% 0.58/0.77              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77           (k1_zfmisc_1 @ 
% 0.58/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('25', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77           (k1_zfmisc_1 @ 
% 0.58/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77             (k1_zfmisc_1 @ 
% 0.58/0.77              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '27'])).
% 0.58/0.77  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77             (k1_zfmisc_1 @ 
% 0.58/0.77              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.77      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77         (k1_zfmisc_1 @ 
% 0.58/0.77          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77        | (v2_struct_0 @ sk_A)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['18', '31'])).
% 0.58/0.77  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77           (k1_zfmisc_1 @ 
% 0.58/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.77      inference('clc', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf(redefinition_r2_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.77         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.58/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X3)
% 0.58/0.77          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.58/0.77          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.58/0.77          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.58/0.77          | ((X0) != (X3)))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.58/0.77          | ~ (v1_funct_1 @ X3)
% 0.58/0.77          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.58/0.77          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '38'])).
% 0.58/0.77  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d5_tmap_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.77             ( l1_pre_topc @ B ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_pre_topc @ C @ A ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m1_pre_topc @ D @ A ) =>
% 0.58/0.77                   ( ![E:$i]:
% 0.58/0.77                     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.77                         ( v1_funct_2 @
% 0.58/0.77                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                         ( m1_subset_1 @
% 0.58/0.77                           E @ 
% 0.58/0.77                           ( k1_zfmisc_1 @
% 0.58/0.77                             ( k2_zfmisc_1 @
% 0.58/0.77                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                       ( ( m1_pre_topc @ D @ C ) =>
% 0.58/0.77                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.58/0.77                           ( k2_partfun1 @
% 0.58/0.77                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.58/0.77                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X12)
% 0.58/0.77          | ~ (v2_pre_topc @ X12)
% 0.58/0.77          | ~ (l1_pre_topc @ X12)
% 0.58/0.77          | ~ (m1_pre_topc @ X13 @ X14)
% 0.58/0.77          | ~ (m1_pre_topc @ X13 @ X15)
% 0.58/0.77          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.58/0.77                 X16 @ (u1_struct_0 @ X13)))
% 0.58/0.77          | ~ (m1_subset_1 @ X16 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.58/0.77          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.58/0.77          | ~ (v1_funct_1 @ X16)
% 0.58/0.77          | ~ (m1_pre_topc @ X15 @ X14)
% 0.58/0.77          | ~ (l1_pre_topc @ X14)
% 0.58/0.77          | ~ (v2_pre_topc @ X14)
% 0.58/0.77          | (v2_struct_0 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.77  thf('45', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['41', '49'])).
% 0.58/0.77  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_D)))
% 0.58/0.77        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['40', '53'])).
% 0.58/0.77  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d4_tmap_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.77             ( l1_pre_topc @ B ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.77                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                 ( m1_subset_1 @
% 0.58/0.77                   C @ 
% 0.58/0.77                   ( k1_zfmisc_1 @
% 0.58/0.77                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m1_pre_topc @ D @ A ) =>
% 0.58/0.77                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.58/0.77                     ( k2_partfun1 @
% 0.58/0.77                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.58/0.77                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('57', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X8)
% 0.58/0.77          | ~ (v2_pre_topc @ X8)
% 0.58/0.77          | ~ (l1_pre_topc @ X8)
% 0.58/0.77          | ~ (m1_pre_topc @ X9 @ X10)
% 0.58/0.77          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.58/0.77                 X11 @ (u1_struct_0 @ X9)))
% 0.58/0.77          | ~ (m1_subset_1 @ X11 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.58/0.77          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.58/0.77          | ~ (v1_funct_1 @ X11)
% 0.58/0.77          | ~ (l1_pre_topc @ X10)
% 0.58/0.77          | ~ (v2_pre_topc @ X10)
% 0.58/0.77          | (v2_struct_0 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.58/0.77  thf('58', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_C)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_C)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_C)
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.77  thf('59', plain, ((v2_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.58/0.77  thf('60', plain, ((l1_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.77  thf('61', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('64', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_C)
% 0.58/0.77          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['58', '59', '60', '61', '62', '63', '64'])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_D)))
% 0.58/0.77        | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['55', '65'])).
% 0.58/0.77  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.58/0.77      inference('clc', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.58/0.77         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.58/0.77            (u1_struct_0 @ sk_D)))),
% 0.58/0.77      inference('clc', [status(thm)], ['68', '69'])).
% 0.58/0.77  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['54', '70', '71'])).
% 0.58/0.77  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('74', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.58/0.77      inference('clc', [status(thm)], ['72', '73'])).
% 0.58/0.77  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('77', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('78', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('80', plain,
% 0.58/0.77      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.58/0.77      inference('demod', [status(thm)], ['39', '76', '77', '78', '79'])).
% 0.58/0.77  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('82', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('83', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('84', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X17 @ X18)
% 0.58/0.77          | ~ (m1_pre_topc @ X19 @ X18)
% 0.58/0.77          | ~ (l1_pre_topc @ X20)
% 0.58/0.77          | ~ (v2_pre_topc @ X20)
% 0.58/0.77          | (v2_struct_0 @ X20)
% 0.58/0.77          | ~ (l1_pre_topc @ X18)
% 0.58/0.77          | ~ (v2_pre_topc @ X18)
% 0.58/0.77          | (v2_struct_0 @ X18)
% 0.58/0.77          | ~ (v1_funct_1 @ X21)
% 0.58/0.77          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.58/0.77          | ~ (m1_subset_1 @ X21 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.58/0.77          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.58/0.77  thf('85', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['83', '84'])).
% 0.58/0.77  thf('86', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('87', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('90', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.58/0.77  thf('91', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['82', '90'])).
% 0.58/0.77  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('94', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.58/0.77      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.58/0.77  thf('95', plain,
% 0.58/0.77      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77        | (v2_struct_0 @ sk_A)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['81', '94'])).
% 0.58/0.77  thf('96', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('97', plain,
% 0.58/0.77      (((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77        | (v2_struct_0 @ sk_A)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['95', '96'])).
% 0.58/0.77  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('99', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.58/0.77      inference('clc', [status(thm)], ['97', '98'])).
% 0.58/0.77  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('101', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['99', '100'])).
% 0.58/0.77  thf('102', plain,
% 0.58/0.77      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.58/0.77      inference('demod', [status(thm)], ['80', '101'])).
% 0.58/0.77  thf('103', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('105', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('106', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X17 @ X18)
% 0.58/0.77          | ~ (m1_pre_topc @ X19 @ X18)
% 0.58/0.77          | ~ (l1_pre_topc @ X20)
% 0.58/0.77          | ~ (v2_pre_topc @ X20)
% 0.58/0.77          | (v2_struct_0 @ X20)
% 0.58/0.77          | ~ (l1_pre_topc @ X18)
% 0.58/0.77          | ~ (v2_pre_topc @ X18)
% 0.58/0.77          | (v2_struct_0 @ X18)
% 0.58/0.77          | ~ (v1_funct_1 @ X21)
% 0.58/0.77          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.58/0.77          | ~ (m1_subset_1 @ X21 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.58/0.77          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.58/0.77             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.58/0.77  thf('107', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.77  thf('108', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('109', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('110', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('112', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | (v2_struct_0 @ X1)
% 0.58/0.77          | ~ (v2_pre_topc @ X1)
% 0.58/0.77          | ~ (l1_pre_topc @ X1)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.58/0.77      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.58/0.77  thf('113', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['104', '112'])).
% 0.58/0.77  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('116', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.58/0.77             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.58/0.77  thf('117', plain,
% 0.58/0.77      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v2_struct_0 @ sk_A)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['103', '116'])).
% 0.58/0.77  thf('118', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('119', plain,
% 0.58/0.77      (((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v2_struct_0 @ sk_A)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['117', '118'])).
% 0.58/0.77  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('121', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.77      inference('clc', [status(thm)], ['119', '120'])).
% 0.58/0.77  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('123', plain,
% 0.58/0.77      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['121', '122'])).
% 0.58/0.77  thf('124', plain,
% 0.58/0.77      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77        (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('demod', [status(thm)], ['102', '123'])).
% 0.58/0.77  thf('125', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('126', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('127', plain,
% 0.58/0.77      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['125', '126'])).
% 0.58/0.77  thf(t77_tmap_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.58/0.77             ( l1_pre_topc @ B ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.77                   ( ![E:$i]:
% 0.58/0.77                     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.77                         ( v1_funct_2 @
% 0.58/0.77                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                         ( m1_subset_1 @
% 0.58/0.77                           E @ 
% 0.58/0.77                           ( k1_zfmisc_1 @
% 0.58/0.77                             ( k2_zfmisc_1 @
% 0.58/0.77                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                       ( ![F:$i]:
% 0.58/0.77                         ( ( ( v1_funct_1 @ F ) & 
% 0.58/0.77                             ( v1_funct_2 @
% 0.58/0.77                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                             ( m1_subset_1 @
% 0.58/0.77                               F @ 
% 0.58/0.77                               ( k1_zfmisc_1 @
% 0.58/0.77                                 ( k2_zfmisc_1 @
% 0.58/0.77                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                           ( ( ( r2_funct_2 @
% 0.58/0.77                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.58/0.77                               ( m1_pre_topc @ D @ C ) ) =>
% 0.58/0.77                             ( r2_funct_2 @
% 0.58/0.77                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.58/0.77                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('128', plain,
% 0.58/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X22)
% 0.58/0.77          | ~ (v2_pre_topc @ X22)
% 0.58/0.77          | ~ (l1_pre_topc @ X22)
% 0.58/0.77          | (v2_struct_0 @ X23)
% 0.58/0.77          | ~ (m1_pre_topc @ X23 @ X24)
% 0.58/0.77          | ~ (v1_funct_1 @ X25)
% 0.58/0.77          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X22))
% 0.58/0.77          | ~ (m1_subset_1 @ X25 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X22))))
% 0.58/0.77          | (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22) @ 
% 0.58/0.77             (k3_tmap_1 @ X24 @ X22 @ X26 @ X23 @ X25) @ 
% 0.58/0.77             (k2_tmap_1 @ X24 @ X22 @ X27 @ X23))
% 0.58/0.77          | ~ (r2_funct_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X22) @ X25 @ 
% 0.58/0.77               (k2_tmap_1 @ X24 @ X22 @ X27 @ X26))
% 0.58/0.77          | ~ (m1_pre_topc @ X23 @ X26)
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 0.58/0.77          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 0.58/0.77          | ~ (v1_funct_1 @ X27)
% 0.58/0.77          | ~ (m1_pre_topc @ X26 @ X24)
% 0.58/0.77          | (v2_struct_0 @ X26)
% 0.58/0.77          | ~ (l1_pre_topc @ X24)
% 0.58/0.77          | ~ (v2_pre_topc @ X24)
% 0.58/0.77          | (v2_struct_0 @ X24))),
% 0.58/0.77      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.58/0.77  thf('129', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X1)
% 0.58/0.77          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.58/0.77          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.58/0.77          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.58/0.77          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77          | ~ (m1_pre_topc @ X2 @ X0)
% 0.58/0.77          | (v2_struct_0 @ X2)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['127', '128'])).
% 0.58/0.77  thf('130', plain,
% 0.58/0.77      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['121', '122'])).
% 0.58/0.77  thf('131', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['99', '100'])).
% 0.58/0.77  thf('132', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('133', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('134', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X1)
% 0.58/0.77          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.58/0.77          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.58/0.77          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.58/0.77          | ~ (m1_pre_topc @ X2 @ X0)
% 0.58/0.77          | (v2_struct_0 @ X2)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.58/0.77  thf('135', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ~ (m1_subset_1 @ sk_F @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_C)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['124', '134'])).
% 0.58/0.77  thf('136', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_F @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('137', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('138', plain, ((v1_funct_1 @ sk_F)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('139', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('140', plain, ((l1_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.77  thf('141', plain, ((v2_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.58/0.77  thf('142', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['135', '136', '137', '138', '139', '140', '141'])).
% 0.58/0.77  thf('143', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | (v2_struct_0 @ sk_D)
% 0.58/0.77        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.58/0.77        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.58/0.77        | (v2_struct_0 @ sk_E)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['17', '142'])).
% 0.58/0.77  thf('144', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('145', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '16'])).
% 0.58/0.77  thf('146', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('147', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('148', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X12)
% 0.58/0.77          | ~ (v2_pre_topc @ X12)
% 0.58/0.77          | ~ (l1_pre_topc @ X12)
% 0.58/0.77          | ~ (m1_pre_topc @ X13 @ X14)
% 0.58/0.77          | ~ (m1_pre_topc @ X13 @ X15)
% 0.58/0.77          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.58/0.77                 X16 @ (u1_struct_0 @ X13)))
% 0.58/0.77          | ~ (m1_subset_1 @ X16 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.58/0.77          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.58/0.77          | ~ (v1_funct_1 @ X16)
% 0.58/0.77          | ~ (m1_pre_topc @ X15 @ X14)
% 0.58/0.77          | ~ (l1_pre_topc @ X14)
% 0.58/0.77          | ~ (v2_pre_topc @ X14)
% 0.58/0.77          | (v2_struct_0 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.58/0.77  thf('149', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.58/0.77              (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77                 (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['147', '148'])).
% 0.58/0.77  thf('150', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('151', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('152', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.58/0.77              (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77                 (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.58/0.77  thf('153', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('154', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['99', '100'])).
% 0.58/0.77  thf('155', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('156', plain,
% 0.58/0.77      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['121', '122'])).
% 0.58/0.77  thf('157', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('158', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('159', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['152', '153', '154', '155', '156', '157', '158'])).
% 0.58/0.77  thf('160', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (l1_pre_topc @ sk_C)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['146', '159'])).
% 0.58/0.77  thf('161', plain, ((l1_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.77  thf('162', plain, ((v2_pre_topc @ sk_C)),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.58/0.77  thf('163', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.58/0.77  thf('164', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.58/0.77        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['145', '163'])).
% 0.58/0.77  thf('165', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('166', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('167', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X8)
% 0.58/0.77          | ~ (v2_pre_topc @ X8)
% 0.58/0.77          | ~ (l1_pre_topc @ X8)
% 0.58/0.77          | ~ (m1_pre_topc @ X9 @ X10)
% 0.58/0.77          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.58/0.77                 X11 @ (u1_struct_0 @ X9)))
% 0.58/0.77          | ~ (m1_subset_1 @ X11 @ 
% 0.58/0.77               (k1_zfmisc_1 @ 
% 0.58/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.58/0.77          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.58/0.77          | ~ (v1_funct_1 @ X11)
% 0.58/0.77          | ~ (l1_pre_topc @ X10)
% 0.58/0.77          | ~ (v2_pre_topc @ X10)
% 0.58/0.77          | (v2_struct_0 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.58/0.77  thf('168', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_D)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_D)
% 0.58/0.77          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77              (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77                 (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ~ (l1_pre_topc @ sk_B)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_B)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['166', '167'])).
% 0.58/0.77  thf('169', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('170', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X4 @ X5)
% 0.58/0.77          | (v2_pre_topc @ X4)
% 0.58/0.77          | ~ (l1_pre_topc @ X5)
% 0.58/0.77          | ~ (v2_pre_topc @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.58/0.77  thf('171', plain,
% 0.58/0.77      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.58/0.77      inference('sup-', [status(thm)], ['169', '170'])).
% 0.58/0.77  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('174', plain, ((v2_pre_topc @ sk_D)),
% 0.58/0.77      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.58/0.77  thf('175', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('176', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.77  thf('177', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.58/0.77      inference('sup-', [status(thm)], ['175', '176'])).
% 0.58/0.77  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('179', plain, ((l1_pre_topc @ sk_D)),
% 0.58/0.77      inference('demod', [status(thm)], ['177', '178'])).
% 0.58/0.77  thf('180', plain, ((l1_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('181', plain, ((v2_pre_topc @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('182', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.58/0.77          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77              (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.58/0.77                 (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['168', '174', '179', '180', '181'])).
% 0.58/0.77  thf('183', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('184', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('185', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('186', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('187', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['182', '183', '184', '185', '186'])).
% 0.58/0.77  thf('188', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['99', '100'])).
% 0.58/0.77  thf('189', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_D)
% 0.58/0.77          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['187', '188'])).
% 0.58/0.77  thf('190', plain,
% 0.58/0.77      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['121', '122'])).
% 0.58/0.77  thf('191', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_D)
% 0.58/0.77          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['189', '190'])).
% 0.58/0.77  thf('192', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.58/0.77        | (v2_struct_0 @ sk_D))),
% 0.58/0.77      inference('sup-', [status(thm)], ['165', '191'])).
% 0.58/0.77  thf('193', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('194', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_D)
% 0.58/0.77        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E))))),
% 0.58/0.77      inference('clc', [status(thm)], ['192', '193'])).
% 0.58/0.77  thf('195', plain, (~ (v2_struct_0 @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('196', plain,
% 0.58/0.77      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77         sk_E)
% 0.58/0.77         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['194', '195'])).
% 0.58/0.77  thf('197', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('198', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['164', '196', '197'])).
% 0.58/0.77  thf('199', plain, (~ (v2_struct_0 @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('200', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['198', '199'])).
% 0.58/0.77  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('202', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.58/0.77      inference('clc', [status(thm)], ['200', '201'])).
% 0.58/0.77  thf('203', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | (v2_struct_0 @ sk_D)
% 0.58/0.77        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.58/0.77        | (v2_struct_0 @ sk_E)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['143', '144', '202'])).
% 0.58/0.77  thf('204', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)) @ 
% 0.58/0.77          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('205', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('206', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.58/0.77      inference('demod', [status(thm)], ['204', '205'])).
% 0.58/0.77  thf('207', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('208', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.58/0.77  thf('209', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_E)))
% 0.58/0.77        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['207', '208'])).
% 0.58/0.77  thf('210', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '16'])).
% 0.58/0.77  thf('211', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_C)
% 0.58/0.77          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 sk_F @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['58', '59', '60', '61', '62', '63', '64'])).
% 0.58/0.77  thf('212', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_E)))
% 0.58/0.77        | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['210', '211'])).
% 0.58/0.77  thf('213', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('214', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C)
% 0.58/0.77        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.58/0.77      inference('clc', [status(thm)], ['212', '213'])).
% 0.58/0.77  thf('215', plain, (~ (v2_struct_0 @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('216', plain,
% 0.58/0.77      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.58/0.77         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.58/0.77            (u1_struct_0 @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['214', '215'])).
% 0.58/0.77  thf('217', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '16'])).
% 0.58/0.77  thf('218', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.58/0.77            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['209', '216', '217'])).
% 0.58/0.77  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('220', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.58/0.77            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['218', '219'])).
% 0.58/0.77  thf('221', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('222', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.58/0.77         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.58/0.77      inference('clc', [status(thm)], ['220', '221'])).
% 0.58/0.77  thf('223', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.58/0.77          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.58/0.77      inference('demod', [status(thm)], ['206', '222'])).
% 0.58/0.77  thf('224', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('225', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('226', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X0)
% 0.58/0.77          | ~ (v2_pre_topc @ X0)
% 0.58/0.77          | ~ (l1_pre_topc @ X0)
% 0.58/0.77          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.58/0.77          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.58/0.77          | ~ (m1_pre_topc @ X1 @ X0)
% 0.58/0.77          | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['152', '153', '154', '155', '156', '157', '158'])).
% 0.58/0.77  thf('227', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['225', '226'])).
% 0.58/0.77  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('229', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('230', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_B)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.77          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.58/0.77          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.58/0.77              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['227', '228', '229'])).
% 0.58/0.77  thf('231', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.58/0.77        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['224', '230'])).
% 0.58/0.77  thf('232', plain,
% 0.58/0.77      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77         sk_E)
% 0.58/0.77         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['194', '195'])).
% 0.58/0.77  thf('233', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('234', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.58/0.77        | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['231', '232', '233'])).
% 0.58/0.77  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('236', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.58/0.77      inference('clc', [status(thm)], ['234', '235'])).
% 0.58/0.77  thf('237', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('238', plain,
% 0.58/0.77      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.58/0.77         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.58/0.77         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.58/0.77            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.58/0.77      inference('clc', [status(thm)], ['236', '237'])).
% 0.58/0.77  thf('239', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.58/0.77           sk_E) @ 
% 0.58/0.77          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.58/0.77      inference('demod', [status(thm)], ['223', '238'])).
% 0.58/0.77  thf('240', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_B)
% 0.58/0.77        | (v2_struct_0 @ sk_E)
% 0.58/0.77        | (v2_struct_0 @ sk_D)
% 0.58/0.77        | (v2_struct_0 @ sk_C))),
% 0.58/0.77      inference('sup-', [status(thm)], ['203', '239'])).
% 0.58/0.77  thf('241', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('242', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.58/0.77      inference('sup-', [status(thm)], ['240', '241'])).
% 0.58/0.77  thf('243', plain, (~ (v2_struct_0 @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('244', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.58/0.77      inference('clc', [status(thm)], ['242', '243'])).
% 0.58/0.77  thf('245', plain, (~ (v2_struct_0 @ sk_E)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('246', plain, ((v2_struct_0 @ sk_D)),
% 0.58/0.77      inference('clc', [status(thm)], ['244', '245'])).
% 0.58/0.77  thf('247', plain, ($false), inference('demod', [status(thm)], ['0', '246'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
