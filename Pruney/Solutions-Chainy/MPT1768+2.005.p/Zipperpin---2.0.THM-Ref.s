%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hM2tbdljMU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:08 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  250 (2322 expanded)
%              Number of leaves         :   28 ( 678 expanded)
%              Depth                    :   29
%              Number of atoms          : 3163 (94904 expanded)
%              Number of equality atoms :   54 ( 276 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_pre_topc @ X25 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ ( k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ ( k2_tmap_1 @ X20 @ X18 @ X22 @ X19 ) ) @ ( k2_tmap_1 @ X20 @ X18 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_E @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ X0 @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('32',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
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
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
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

thf('65',plain,(
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

thf('66',plain,(
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
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('69',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
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

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('96',plain,(
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
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('112',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','112','113','114'])).

thf('116',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('120',plain,(
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
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('132',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
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
    inference(demod,[status(thm)],['115','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('140',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','141'])).

thf('143',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('145',plain,(
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

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('149',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('155',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('159',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','152','157','158','159','160'])).

thf('162',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['143','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','174','175'])).

thf('177',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('179',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['179','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
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
    inference(demod,[status(thm)],['115','136'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['197','203'])).

thf('205',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('206',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['196','211'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['0','219'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hM2tbdljMU
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 310 iterations in 0.214s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.44/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.44/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.68  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.44/0.68  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.44/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.68  thf(t79_tmap_1, conjecture,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.44/0.68             ( l1_pre_topc @ B ) ) =>
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.44/0.68               ( ![D:$i]:
% 0.44/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.44/0.68                   ( ![E:$i]:
% 0.44/0.68                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.44/0.68                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.44/0.68                         ( ![F:$i]:
% 0.44/0.68                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.68                               ( v1_funct_2 @
% 0.44/0.68                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.68                               ( m1_subset_1 @
% 0.44/0.68                                 F @ 
% 0.44/0.68                                 ( k1_zfmisc_1 @
% 0.44/0.68                                   ( k2_zfmisc_1 @
% 0.44/0.68                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68                             ( r2_funct_2 @
% 0.44/0.68                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.44/0.68                               ( k3_tmap_1 @
% 0.44/0.68                                 A @ B @ D @ E @ 
% 0.44/0.68                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.44/0.68                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i]:
% 0.44/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.68            ( l1_pre_topc @ A ) ) =>
% 0.44/0.68          ( ![B:$i]:
% 0.44/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.44/0.68                ( l1_pre_topc @ B ) ) =>
% 0.44/0.68              ( ![C:$i]:
% 0.44/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.44/0.68                  ( ![D:$i]:
% 0.44/0.68                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.44/0.68                      ( ![E:$i]:
% 0.44/0.68                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.44/0.68                          ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.44/0.68                            ( ![F:$i]:
% 0.44/0.68                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.68                                  ( v1_funct_2 @
% 0.44/0.68                                    F @ ( u1_struct_0 @ C ) @ 
% 0.44/0.68                                    ( u1_struct_0 @ B ) ) & 
% 0.44/0.68                                  ( m1_subset_1 @
% 0.44/0.68                                    F @ 
% 0.44/0.68                                    ( k1_zfmisc_1 @
% 0.44/0.68                                      ( k2_zfmisc_1 @
% 0.44/0.68                                        ( u1_struct_0 @ C ) @ 
% 0.44/0.68                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68                                ( r2_funct_2 @
% 0.44/0.68                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.44/0.68                                  ( k3_tmap_1 @
% 0.44/0.68                                    A @ B @ D @ E @ 
% 0.44/0.68                                    ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.44/0.68                                  ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t79_tmap_1])).
% 0.44/0.68  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('2', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t7_tsep_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.44/0.68           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.44/0.68  thf('4', plain,
% 0.44/0.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X23 @ X24)
% 0.44/0.68          | (m1_pre_topc @ X25 @ X24)
% 0.44/0.68          | ~ (m1_pre_topc @ X25 @ X23)
% 0.44/0.68          | ~ (l1_pre_topc @ X24)
% 0.44/0.68          | ~ (v2_pre_topc @ X24))),
% 0.44/0.68      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (v2_pre_topc @ sk_C)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | (m1_pre_topc @ X0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.68  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(cc1_pre_topc, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ X1)
% 0.44/0.68          | (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1))),
% 0.44/0.68      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('11', plain, ((v2_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.44/0.68  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(dt_m1_pre_topc, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( l1_pre_topc @ A ) =>
% 0.44/0.68       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (![X2 : $i, X3 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.44/0.68  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.68  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.44/0.68      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.44/0.68  thf('18', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.44/0.68      inference('sup-', [status(thm)], ['2', '17'])).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t78_tmap_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.44/0.68             ( l1_pre_topc @ B ) ) =>
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.44/0.68               ( ![D:$i]:
% 0.44/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.44/0.68                   ( ![E:$i]:
% 0.44/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.68                         ( v1_funct_2 @
% 0.44/0.68                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.68                         ( m1_subset_1 @
% 0.44/0.68                           E @ 
% 0.44/0.68                           ( k1_zfmisc_1 @
% 0.44/0.68                             ( k2_zfmisc_1 @
% 0.44/0.68                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68                       ( ( m1_pre_topc @ C @ D ) =>
% 0.44/0.68                         ( r2_funct_2 @
% 0.44/0.68                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.44/0.68                           ( k3_tmap_1 @
% 0.44/0.68                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.44/0.68                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.68  thf('20', plain,
% 0.44/0.68      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X18)
% 0.44/0.68          | ~ (v2_pre_topc @ X18)
% 0.44/0.68          | ~ (l1_pre_topc @ X18)
% 0.44/0.68          | (v2_struct_0 @ X19)
% 0.44/0.68          | ~ (m1_pre_topc @ X19 @ X20)
% 0.44/0.68          | ~ (m1_pre_topc @ X21 @ X19)
% 0.44/0.68          | (r2_funct_2 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.44/0.68             (k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ 
% 0.44/0.68              (k2_tmap_1 @ X20 @ X18 @ X22 @ X19)) @ 
% 0.44/0.68             (k2_tmap_1 @ X20 @ X18 @ X22 @ X21))
% 0.44/0.68          | ~ (m1_subset_1 @ X22 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.44/0.68          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.44/0.68          | ~ (v1_funct_1 @ X22)
% 0.44/0.68          | ~ (m1_pre_topc @ X21 @ X20)
% 0.44/0.68          | (v2_struct_0 @ X21)
% 0.44/0.68          | ~ (l1_pre_topc @ X20)
% 0.44/0.68          | ~ (v2_pre_topc @ X20)
% 0.44/0.68          | (v2_struct_0 @ X20))),
% 0.44/0.68      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.44/0.68  thf('21', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_C)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_C)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.44/0.68             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.68  thf('22', plain, ((v2_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.44/0.68  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('28', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.44/0.68             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)],
% 0.44/0.68                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.44/0.68  thf('29', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_E @ X0)
% 0.44/0.68          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68             (k3_tmap_1 @ sk_C @ sk_B @ X0 @ sk_E @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)) @ 
% 0.44/0.68             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.44/0.68          | (v2_struct_0 @ sk_E)
% 0.44/0.68          | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['18', '28'])).
% 0.44/0.68  thf('30', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | (v2_struct_0 @ sk_E)
% 0.44/0.68        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.44/0.68           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.44/0.68        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['1', '29'])).
% 0.44/0.68  thf('31', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.44/0.68      inference('sup-', [status(thm)], ['2', '17'])).
% 0.44/0.68  thf('32', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('35', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(dt_k3_tmap_1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.44/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.68         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.44/0.68         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.44/0.68         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.44/0.68         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.68         ( m1_subset_1 @
% 0.44/0.68           E @ 
% 0.44/0.68           ( k1_zfmisc_1 @
% 0.44/0.68             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.44/0.68         ( v1_funct_2 @
% 0.44/0.68           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.44/0.68           ( u1_struct_0 @ B ) ) & 
% 0.44/0.68         ( m1_subset_1 @
% 0.44/0.68           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.44/0.68           ( k1_zfmisc_1 @
% 0.44/0.68             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.44/0.68  thf('36', plain,
% 0.44/0.68      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X13 @ X14)
% 0.44/0.68          | ~ (m1_pre_topc @ X15 @ X14)
% 0.44/0.68          | ~ (l1_pre_topc @ X16)
% 0.44/0.68          | ~ (v2_pre_topc @ X16)
% 0.44/0.68          | (v2_struct_0 @ X16)
% 0.44/0.68          | ~ (l1_pre_topc @ X14)
% 0.44/0.68          | ~ (v2_pre_topc @ X14)
% 0.44/0.68          | (v2_struct_0 @ X14)
% 0.44/0.68          | ~ (v1_funct_1 @ X17)
% 0.44/0.68          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.44/0.68          | ~ (m1_subset_1 @ X17 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.44/0.68          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.44/0.68             (k1_zfmisc_1 @ 
% 0.44/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.44/0.68  thf('37', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68           (k1_zfmisc_1 @ 
% 0.44/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.68  thf('38', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('39', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('42', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68           (k1_zfmisc_1 @ 
% 0.44/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.44/0.68  thf('43', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68             (k1_zfmisc_1 @ 
% 0.44/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.44/0.68      inference('sup-', [status(thm)], ['34', '42'])).
% 0.44/0.68  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('46', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68             (k1_zfmisc_1 @ 
% 0.44/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.44/0.68      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.44/0.68  thf('47', plain,
% 0.44/0.68      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.44/0.68         (k1_zfmisc_1 @ 
% 0.44/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.44/0.68        | (v2_struct_0 @ sk_A)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['33', '46'])).
% 0.44/0.68  thf('48', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('50', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(d5_tmap_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.44/0.68             ( l1_pre_topc @ B ) ) =>
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( m1_pre_topc @ C @ A ) =>
% 0.44/0.68               ( ![D:$i]:
% 0.44/0.68                 ( ( m1_pre_topc @ D @ A ) =>
% 0.44/0.68                   ( ![E:$i]:
% 0.44/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.68                         ( v1_funct_2 @
% 0.44/0.68                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.68                         ( m1_subset_1 @
% 0.44/0.68                           E @ 
% 0.44/0.68                           ( k1_zfmisc_1 @
% 0.44/0.68                             ( k2_zfmisc_1 @
% 0.44/0.68                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68                       ( ( m1_pre_topc @ D @ C ) =>
% 0.44/0.68                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.44/0.68                           ( k2_partfun1 @
% 0.44/0.68                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.44/0.68                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.68  thf('51', plain,
% 0.44/0.68      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X8)
% 0.44/0.68          | ~ (v2_pre_topc @ X8)
% 0.44/0.68          | ~ (l1_pre_topc @ X8)
% 0.44/0.68          | ~ (m1_pre_topc @ X9 @ X10)
% 0.44/0.68          | ~ (m1_pre_topc @ X9 @ X11)
% 0.44/0.68          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.44/0.68                 X12 @ (u1_struct_0 @ X9)))
% 0.44/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.44/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.44/0.68          | ~ (v1_funct_1 @ X12)
% 0.44/0.68          | ~ (m1_pre_topc @ X11 @ X10)
% 0.44/0.68          | ~ (l1_pre_topc @ X10)
% 0.44/0.68          | ~ (v2_pre_topc @ X10)
% 0.44/0.68          | (v2_struct_0 @ X10))),
% 0.44/0.68      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.44/0.68  thf('52', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.68  thf('53', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('54', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('57', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.44/0.68  thf('58', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['49', '57'])).
% 0.44/0.68  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('61', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | (v2_struct_0 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.68  thf('62', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_D)))
% 0.44/0.68        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['48', '61'])).
% 0.44/0.68  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('64', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(d4_tmap_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.44/0.68             ( l1_pre_topc @ B ) ) =>
% 0.44/0.68           ( ![C:$i]:
% 0.44/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.68                 ( m1_subset_1 @
% 0.44/0.68                   C @ 
% 0.44/0.68                   ( k1_zfmisc_1 @
% 0.44/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.68               ( ![D:$i]:
% 0.44/0.68                 ( ( m1_pre_topc @ D @ A ) =>
% 0.44/0.68                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.44/0.68                     ( k2_partfun1 @
% 0.44/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.44/0.68                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.68  thf('65', plain,
% 0.44/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X4)
% 0.44/0.68          | ~ (v2_pre_topc @ X4)
% 0.44/0.68          | ~ (l1_pre_topc @ X4)
% 0.44/0.68          | ~ (m1_pre_topc @ X5 @ X6)
% 0.44/0.68          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.44/0.68                 (u1_struct_0 @ X5)))
% 0.44/0.68          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.44/0.68          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.44/0.68          | ~ (v1_funct_1 @ X7)
% 0.44/0.68          | ~ (l1_pre_topc @ X6)
% 0.44/0.68          | ~ (v2_pre_topc @ X6)
% 0.44/0.68          | (v2_struct_0 @ X6))),
% 0.44/0.68      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.44/0.68  thf('66', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_C)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_C)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_C)
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.68  thf('67', plain, ((v2_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.44/0.68  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('69', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('70', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('73', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_C)
% 0.44/0.68          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)],
% 0.44/0.68                ['66', '67', '68', '69', '70', '71', '72'])).
% 0.44/0.68  thf('74', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_D)))
% 0.44/0.68        | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['63', '73'])).
% 0.44/0.68  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('76', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.44/0.68      inference('clc', [status(thm)], ['74', '75'])).
% 0.44/0.68  thf('77', plain, (~ (v2_struct_0 @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('78', plain,
% 0.44/0.68      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.44/0.68         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.44/0.68            (u1_struct_0 @ sk_D)))),
% 0.44/0.68      inference('clc', [status(thm)], ['76', '77'])).
% 0.44/0.68  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('80', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['62', '78', '79'])).
% 0.44/0.68  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('82', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.44/0.68      inference('clc', [status(thm)], ['80', '81'])).
% 0.44/0.68  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('84', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('clc', [status(thm)], ['82', '83'])).
% 0.44/0.68  thf('85', plain,
% 0.44/0.68      (((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68         (k1_zfmisc_1 @ 
% 0.44/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.44/0.68        | (v2_struct_0 @ sk_A)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['47', '84'])).
% 0.44/0.68  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('87', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68           (k1_zfmisc_1 @ 
% 0.44/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.44/0.68      inference('clc', [status(thm)], ['85', '86'])).
% 0.44/0.68  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('89', plain,
% 0.44/0.68      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('clc', [status(thm)], ['87', '88'])).
% 0.44/0.68  thf('90', plain,
% 0.44/0.68      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X8)
% 0.44/0.68          | ~ (v2_pre_topc @ X8)
% 0.44/0.68          | ~ (l1_pre_topc @ X8)
% 0.44/0.68          | ~ (m1_pre_topc @ X9 @ X10)
% 0.44/0.68          | ~ (m1_pre_topc @ X9 @ X11)
% 0.44/0.68          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.44/0.68                 X12 @ (u1_struct_0 @ X9)))
% 0.44/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.44/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.44/0.68          | ~ (v1_funct_1 @ X12)
% 0.44/0.68          | ~ (m1_pre_topc @ X11 @ X10)
% 0.44/0.68          | ~ (l1_pre_topc @ X10)
% 0.44/0.68          | ~ (v2_pre_topc @ X10)
% 0.44/0.68          | (v2_struct_0 @ X10))),
% 0.44/0.68      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.44/0.68  thf('91', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.44/0.68          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.68  thf('92', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('94', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('95', plain,
% 0.44/0.68      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X13 @ X14)
% 0.44/0.68          | ~ (m1_pre_topc @ X15 @ X14)
% 0.44/0.68          | ~ (l1_pre_topc @ X16)
% 0.44/0.68          | ~ (v2_pre_topc @ X16)
% 0.44/0.68          | (v2_struct_0 @ X16)
% 0.44/0.68          | ~ (l1_pre_topc @ X14)
% 0.44/0.68          | ~ (v2_pre_topc @ X14)
% 0.44/0.68          | (v2_struct_0 @ X14)
% 0.44/0.68          | ~ (v1_funct_1 @ X17)
% 0.44/0.68          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.44/0.68          | ~ (m1_subset_1 @ X17 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.44/0.68          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.44/0.68  thf('96', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.68  thf('97', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('98', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('101', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F))
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.44/0.68  thf('102', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['93', '101'])).
% 0.44/0.68  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('105', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)))),
% 0.44/0.68      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.44/0.68  thf('106', plain,
% 0.44/0.68      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.44/0.68        | (v2_struct_0 @ sk_A)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['92', '105'])).
% 0.44/0.68  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('108', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.44/0.68      inference('clc', [status(thm)], ['106', '107'])).
% 0.44/0.68  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('110', plain,
% 0.44/0.68      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.44/0.68      inference('clc', [status(thm)], ['108', '109'])).
% 0.44/0.68  thf('111', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('clc', [status(thm)], ['82', '83'])).
% 0.44/0.68  thf('112', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.68  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('114', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('115', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.44/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['91', '112', '113', '114'])).
% 0.44/0.68  thf('116', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('118', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_F @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('119', plain,
% 0.44/0.68      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X13 @ X14)
% 0.44/0.68          | ~ (m1_pre_topc @ X15 @ X14)
% 0.44/0.68          | ~ (l1_pre_topc @ X16)
% 0.44/0.68          | ~ (v2_pre_topc @ X16)
% 0.44/0.68          | (v2_struct_0 @ X16)
% 0.44/0.68          | ~ (l1_pre_topc @ X14)
% 0.44/0.68          | ~ (v2_pre_topc @ X14)
% 0.44/0.68          | (v2_struct_0 @ X14)
% 0.44/0.68          | ~ (v1_funct_1 @ X17)
% 0.44/0.68          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.44/0.68          | ~ (m1_subset_1 @ X17 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.44/0.68          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.44/0.68             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.44/0.68  thf('120', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('sup-', [status(thm)], ['118', '119'])).
% 0.44/0.68  thf('121', plain,
% 0.44/0.68      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('122', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('123', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('125', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | (v2_struct_0 @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.44/0.68      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.44/0.68  thf('126', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['117', '125'])).
% 0.44/0.68  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('129', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_A)
% 0.44/0.68          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F) @ 
% 0.44/0.68             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.44/0.68  thf('130', plain,
% 0.44/0.68      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.44/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68        | (v2_struct_0 @ sk_A)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['116', '129'])).
% 0.44/0.68  thf('131', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('clc', [status(thm)], ['82', '83'])).
% 0.44/0.68  thf('132', plain,
% 0.44/0.68      (((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68        | (v2_struct_0 @ sk_A)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['130', '131'])).
% 0.44/0.68  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('134', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.44/0.68      inference('clc', [status(thm)], ['132', '133'])).
% 0.44/0.68  thf('135', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('136', plain,
% 0.44/0.68      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('clc', [status(thm)], ['134', '135'])).
% 0.44/0.68  thf('137', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['115', '136'])).
% 0.44/0.68  thf('138', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (l1_pre_topc @ sk_C)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['32', '137'])).
% 0.44/0.68  thf('139', plain, ((l1_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.68  thf('140', plain, ((v2_pre_topc @ sk_C)),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.44/0.68  thf('141', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.44/0.68  thf('142', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.44/0.68        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['31', '141'])).
% 0.44/0.68  thf('143', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('144', plain,
% 0.44/0.68      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68        (k1_zfmisc_1 @ 
% 0.44/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.68      inference('clc', [status(thm)], ['87', '88'])).
% 0.44/0.68  thf('145', plain,
% 0.44/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X4)
% 0.44/0.68          | ~ (v2_pre_topc @ X4)
% 0.44/0.68          | ~ (l1_pre_topc @ X4)
% 0.44/0.68          | ~ (m1_pre_topc @ X5 @ X6)
% 0.44/0.68          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.44/0.68                 (u1_struct_0 @ X5)))
% 0.44/0.68          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.68               (k1_zfmisc_1 @ 
% 0.44/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.44/0.68          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.44/0.68          | ~ (v1_funct_1 @ X7)
% 0.44/0.68          | ~ (l1_pre_topc @ X6)
% 0.44/0.68          | ~ (v2_pre_topc @ X6)
% 0.44/0.68          | (v2_struct_0 @ X6))),
% 0.44/0.68      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.44/0.68  thf('146', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_D)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_D)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_D)
% 0.44/0.68          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['144', '145'])).
% 0.44/0.68  thf('147', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('148', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X0 @ X1)
% 0.44/0.68          | (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X1)
% 0.44/0.68          | ~ (v2_pre_topc @ X1))),
% 0.44/0.68      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.44/0.68  thf('149', plain,
% 0.44/0.68      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.44/0.68      inference('sup-', [status(thm)], ['147', '148'])).
% 0.44/0.68  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('152', plain, ((v2_pre_topc @ sk_D)),
% 0.44/0.68      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.44/0.68  thf('153', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('154', plain,
% 0.44/0.68      (![X2 : $i, X3 : $i]:
% 0.44/0.68         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.44/0.68  thf('155', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.44/0.68      inference('sup-', [status(thm)], ['153', '154'])).
% 0.44/0.68  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('157', plain, ((l1_pre_topc @ sk_D)),
% 0.44/0.68      inference('demod', [status(thm)], ['155', '156'])).
% 0.44/0.68  thf('158', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.68  thf('159', plain, ((l1_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('160', plain, ((v2_pre_topc @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('161', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_D)
% 0.44/0.68          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.44/0.68          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)],
% 0.44/0.68                ['146', '152', '157', '158', '159', '160'])).
% 0.44/0.68  thf('162', plain,
% 0.44/0.68      ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.44/0.68      inference('clc', [status(thm)], ['134', '135'])).
% 0.44/0.68  thf('163', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_D)
% 0.44/0.68          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['161', '162'])).
% 0.44/0.68  thf('164', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.44/0.68        | (v2_struct_0 @ sk_D))),
% 0.44/0.68      inference('sup-', [status(thm)], ['143', '163'])).
% 0.44/0.68  thf('165', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('166', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_D)
% 0.44/0.68        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E))))),
% 0.44/0.68      inference('clc', [status(thm)], ['164', '165'])).
% 0.44/0.68  thf('167', plain, (~ (v2_struct_0 @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('168', plain,
% 0.44/0.68      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68         sk_E)
% 0.44/0.68         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['166', '167'])).
% 0.44/0.68  thf('169', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('170', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['142', '168', '169'])).
% 0.44/0.68  thf('171', plain, (~ (v2_struct_0 @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('172', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['170', '171'])).
% 0.44/0.68  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('174', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.44/0.68      inference('clc', [status(thm)], ['172', '173'])).
% 0.44/0.68  thf('175', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('176', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | (v2_struct_0 @ sk_E)
% 0.44/0.68        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.44/0.68           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.44/0.68        | (v2_struct_0 @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['30', '174', '175'])).
% 0.44/0.68  thf('177', plain,
% 0.44/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)) @ 
% 0.44/0.68          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('178', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.44/0.68         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.44/0.68      inference('clc', [status(thm)], ['82', '83'])).
% 0.44/0.68  thf('179', plain,
% 0.44/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.44/0.68          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.44/0.68      inference('demod', [status(thm)], ['177', '178'])).
% 0.44/0.68  thf('180', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('181', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | (v2_struct_0 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.68  thf('182', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_E)))
% 0.44/0.68        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['180', '181'])).
% 0.44/0.68  thf('183', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.44/0.68      inference('sup-', [status(thm)], ['2', '17'])).
% 0.44/0.68  thf('184', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_C)
% 0.44/0.68          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 sk_F @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)],
% 0.44/0.68                ['66', '67', '68', '69', '70', '71', '72'])).
% 0.44/0.68  thf('185', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_E)))
% 0.44/0.68        | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['183', '184'])).
% 0.44/0.68  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('187', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C)
% 0.44/0.68        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.44/0.68      inference('clc', [status(thm)], ['185', '186'])).
% 0.44/0.68  thf('188', plain, (~ (v2_struct_0 @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('189', plain,
% 0.44/0.68      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.44/0.68         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.44/0.68            (u1_struct_0 @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['187', '188'])).
% 0.44/0.68  thf('190', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.44/0.68      inference('sup-', [status(thm)], ['2', '17'])).
% 0.44/0.68  thf('191', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.44/0.68            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['182', '189', '190'])).
% 0.44/0.68  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('193', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.44/0.68            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['191', '192'])).
% 0.44/0.68  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('195', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.44/0.68         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.44/0.68      inference('clc', [status(thm)], ['193', '194'])).
% 0.44/0.68  thf('196', plain,
% 0.44/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.44/0.68          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.44/0.68      inference('demod', [status(thm)], ['179', '195'])).
% 0.44/0.68  thf('197', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('198', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('199', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((v2_struct_0 @ X0)
% 0.44/0.68          | ~ (v2_pre_topc @ X0)
% 0.44/0.68          | ~ (l1_pre_topc @ X0)
% 0.44/0.68          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.44/0.68          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X1)))
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.44/0.68          | ~ (m1_pre_topc @ X1 @ X0)
% 0.44/0.68          | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['115', '136'])).
% 0.44/0.68  thf('200', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.68          | (v2_struct_0 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['198', '199'])).
% 0.44/0.68  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('202', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('203', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((v2_struct_0 @ sk_B)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.44/0.68          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.44/0.68          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.44/0.68              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.44/0.68          | (v2_struct_0 @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['200', '201', '202'])).
% 0.44/0.68  thf('204', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.44/0.68        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['197', '203'])).
% 0.44/0.68  thf('205', plain,
% 0.44/0.68      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68         sk_E)
% 0.44/0.68         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['166', '167'])).
% 0.44/0.68  thf('206', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('207', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_A)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.44/0.68        | (v2_struct_0 @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['204', '205', '206'])).
% 0.44/0.68  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('209', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.44/0.68      inference('clc', [status(thm)], ['207', '208'])).
% 0.44/0.68  thf('210', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('211', plain,
% 0.44/0.68      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.44/0.68         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.44/0.68         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.44/0.68            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.44/0.68      inference('clc', [status(thm)], ['209', '210'])).
% 0.44/0.68  thf('212', plain,
% 0.44/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.68          (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.44/0.68           sk_E) @ 
% 0.44/0.68          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.44/0.68      inference('demod', [status(thm)], ['196', '211'])).
% 0.44/0.68  thf('213', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_B)
% 0.44/0.68        | (v2_struct_0 @ sk_D)
% 0.44/0.68        | (v2_struct_0 @ sk_E)
% 0.44/0.68        | (v2_struct_0 @ sk_C))),
% 0.44/0.68      inference('sup-', [status(thm)], ['176', '212'])).
% 0.44/0.68  thf('214', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('215', plain,
% 0.44/0.68      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.44/0.68      inference('sup-', [status(thm)], ['213', '214'])).
% 0.44/0.68  thf('216', plain, (~ (v2_struct_0 @ sk_C)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('217', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.44/0.68      inference('clc', [status(thm)], ['215', '216'])).
% 0.44/0.68  thf('218', plain, (~ (v2_struct_0 @ sk_D)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('219', plain, ((v2_struct_0 @ sk_E)),
% 0.44/0.68      inference('clc', [status(thm)], ['217', '218'])).
% 0.44/0.68  thf('220', plain, ($false), inference('demod', [status(thm)], ['0', '219'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
