%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClQELiGeeR

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  230 (1058 expanded)
%              Number of leaves         :   30 ( 323 expanded)
%              Depth                    :   25
%              Number of atoms          : 3089 (37018 expanded)
%              Number of equality atoms :   58 (  86 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
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
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','40','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('52',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('60',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

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

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) @ X13 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('81',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','40','43','44','45'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

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

thf('88',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( k2_tmap_1 @ X7 @ X5 @ X8 @ X6 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X8 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('99',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['75','76'])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('102',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['97','98','99','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','116'])).

thf('118',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) @ X13 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
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
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','132'])).

thf('134',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( k2_tmap_1 @ X7 @ X5 @ X8 @ X6 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X8 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('137',plain,(
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
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('139',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('140',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F ) ) ),
    inference(demod,[status(thm)],['118','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['2','17'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['159','166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['156','172'])).

thf('174',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['174','181'])).

thf('183',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('184',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D ) @ sk_E ) @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['173','189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    $false ),
    inference(demod,[status(thm)],['0','197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ClQELiGeeR
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 116 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(t79_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.52                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.20/0.52                         ( ![F:$i]:
% 0.20/0.52                           ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.52                               ( v1_funct_2 @
% 0.20/0.52                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                               ( m1_subset_1 @
% 0.20/0.52                                 F @ 
% 0.20/0.52                                 ( k1_zfmisc_1 @
% 0.20/0.52                                   ( k2_zfmisc_1 @
% 0.20/0.52                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                             ( r2_funct_2 @
% 0.20/0.52                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.52                               ( k3_tmap_1 @
% 0.20/0.52                                 A @ B @ D @ E @ 
% 0.20/0.52                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.20/0.52                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52                ( l1_pre_topc @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                      ( ![E:$i]:
% 0.20/0.52                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.52                          ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 0.20/0.52                            ( ![F:$i]:
% 0.20/0.52                              ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.52                                  ( v1_funct_2 @
% 0.20/0.52                                    F @ ( u1_struct_0 @ C ) @ 
% 0.20/0.52                                    ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                                  ( m1_subset_1 @
% 0.20/0.52                                    F @ 
% 0.20/0.52                                    ( k1_zfmisc_1 @
% 0.20/0.52                                      ( k2_zfmisc_1 @
% 0.20/0.52                                        ( u1_struct_0 @ C ) @ 
% 0.20/0.52                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                                ( r2_funct_2 @
% 0.20/0.52                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.52                                  ( k3_tmap_1 @
% 0.20/0.52                                    A @ B @ D @ E @ 
% 0.20/0.52                                    ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 0.20/0.52                                  ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t79_tmap_1])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t7_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.52          | (m1_pre_topc @ X25 @ X24)
% 0.20/0.52          | ~ (m1_pre_topc @ X25 @ X23)
% 0.20/0.52          | ~ (l1_pre_topc @ X24)
% 0.20/0.52          | ~ (v2_pre_topc @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ sk_C)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | (m1_pre_topc @ X0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.20/0.52  thf('18', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t78_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                         ( v1_funct_2 @
% 0.20/0.52                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52                         ( m1_subset_1 @
% 0.20/0.52                           E @ 
% 0.20/0.52                           ( k1_zfmisc_1 @
% 0.20/0.52                             ( k2_zfmisc_1 @
% 0.20/0.52                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.52                         ( r2_funct_2 @
% 0.20/0.52                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.52                           ( k3_tmap_1 @
% 0.20/0.52                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.20/0.52                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X18)
% 0.20/0.52          | ~ (v2_pre_topc @ X18)
% 0.20/0.52          | ~ (l1_pre_topc @ X18)
% 0.20/0.52          | (v2_struct_0 @ X19)
% 0.20/0.52          | ~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.52          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.52          | (r2_funct_2 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.20/0.52             (k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ 
% 0.20/0.52              (k2_tmap_1 @ X20 @ X18 @ X22 @ X19)) @ 
% 0.20/0.52             (k2_tmap_1 @ X20 @ X18 @ X22 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.20/0.52          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.20/0.52          | ~ (v1_funct_1 @ X22)
% 0.20/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (l1_pre_topc @ X20)
% 0.20/0.52          | ~ (v2_pre_topc @ X20)
% 0.20/0.52          | (v2_struct_0 @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_C)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52             (k3_tmap_1 @ sk_C @ sk_B @ X1 @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X1)) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_E @ X0)
% 0.20/0.52          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52             (k3_tmap_1 @ sk_C @ sk_B @ X0 @ sk_E @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '29'])).
% 0.20/0.52  thf('31', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '17'])).
% 0.20/0.52  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k2_tmap_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           C @ 
% 0.20/0.52           ( k1_zfmisc_1 @
% 0.20/0.52             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.20/0.52         ( l1_struct_0 @ D ) ) =>
% 0.20/0.52       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.52         ( v1_funct_2 @
% 0.20/0.52           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.20/0.52           ( u1_struct_0 @ B ) ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.20/0.52           ( k1_zfmisc_1 @
% 0.20/0.52             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (l1_struct_0 @ X16)
% 0.20/0.52          | ~ (l1_struct_0 @ X15)
% 0.20/0.52          | ~ (l1_struct_0 @ X17)
% 0.20/0.52          | (v1_funct_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('39', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('40', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '40', '43', '44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (l1_struct_0 @ X16)
% 0.20/0.52          | ~ (l1_struct_0 @ X15)
% 0.20/0.52          | ~ (l1_struct_0 @ X17)
% 0.20/0.52          | (v1_funct_2 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.20/0.52             (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.20/0.52          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (l1_struct_0 @ X16)
% 0.20/0.52          | ~ (l1_struct_0 @ X15)
% 0.20/0.52          | ~ (l1_struct_0 @ X17)
% 0.20/0.52          | (m1_subset_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_C)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('60', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
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
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X12)
% 0.20/0.52          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.20/0.52                 X13 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X13)
% 0.20/0.52          | ~ (m1_pre_topc @ X12 @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '71'])).
% 0.20/0.52  thf('73', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('75', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('79', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('81', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['72', '79', '80', '81'])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '82'])).
% 0.20/0.52  thf('84', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '40', '43', '44', '45'])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52           (k1_zfmisc_1 @ 
% 0.20/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
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
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X5)
% 0.20/0.52          | ~ (v2_pre_topc @ X5)
% 0.20/0.52          | ~ (l1_pre_topc @ X5)
% 0.20/0.52          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.52          | ((k2_tmap_1 @ X7 @ X5 @ X8 @ X6)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X8 @ 
% 0.20/0.52                 (u1_struct_0 @ X6)))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.20/0.52          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (l1_pre_topc @ X7)
% 0.20/0.52          | ~ (v2_pre_topc @ X7)
% 0.20/0.52          | (v2_struct_0 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.52  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['86', '92'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['93'])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['85', '94'])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ((k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ 
% 0.20/0.52              X1)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['95'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      ((~ (l1_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_D)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['84', '96'])).
% 0.20/0.52  thf('98', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('99', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.52  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('105', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['97', '98', '99', '105'])).
% 0.20/0.52  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_D)
% 0.20/0.52        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E))))),
% 0.20/0.52      inference('clc', [status(thm)], ['106', '107'])).
% 0.20/0.52  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.20/0.52         sk_E)
% 0.20/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['108', '109'])).
% 0.20/0.52  thf('111', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['83', '110', '111'])).
% 0.20/0.52  thf('113', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['112', '113'])).
% 0.20/0.52  thf('115', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (((k3_tmap_1 @ sk_C @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.20/0.52      inference('clc', [status(thm)], ['114', '115'])).
% 0.20/0.52  thf('117', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '116'])).
% 0.20/0.52  thf('118', plain,
% 0.20/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)) @ 
% 0.20/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('119', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('120', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('121', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X12)
% 0.20/0.52          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.20/0.52                 X13 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X13)
% 0.20/0.52          | ~ (m1_pre_topc @ X12 @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.52  thf('123', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['121', '122'])).
% 0.20/0.52  thf('124', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('125', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('127', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('128', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.52          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_F)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.20/0.52  thf('129', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['120', '128'])).
% 0.20/0.52  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('132', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.20/0.52  thf('133', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_D)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['119', '132'])).
% 0.20/0.52  thf('134', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('135', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X5)
% 0.20/0.52          | ~ (v2_pre_topc @ X5)
% 0.20/0.52          | ~ (l1_pre_topc @ X5)
% 0.20/0.52          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.52          | ((k2_tmap_1 @ X7 @ X5 @ X8 @ X6)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X8 @ 
% 0.20/0.52                 (u1_struct_0 @ X6)))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.20/0.52          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (l1_pre_topc @ X7)
% 0.20/0.52          | ~ (v2_pre_topc @ X7)
% 0.20/0.52          | (v2_struct_0 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.52  thf('137', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_C)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_C)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_C)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_F)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['135', '136'])).
% 0.20/0.52  thf('138', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('139', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('140', plain, ((v1_funct_1 @ sk_F)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('141', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('143', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('144', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_C)
% 0.20/0.52          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['137', '138', '139', '140', '141', '142', '143'])).
% 0.20/0.52  thf('145', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_D)))
% 0.20/0.52        | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['134', '144'])).
% 0.20/0.52  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('147', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_D))))),
% 0.20/0.52      inference('clc', [status(thm)], ['145', '146'])).
% 0.20/0.52  thf('148', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('149', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)
% 0.20/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.20/0.52            (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['147', '148'])).
% 0.20/0.52  thf('150', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('151', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['133', '149', '150'])).
% 0.20/0.52  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('153', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)))),
% 0.20/0.52      inference('clc', [status(thm)], ['151', '152'])).
% 0.20/0.52  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('155', plain,
% 0.20/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.52         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))),
% 0.20/0.52      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.52  thf('156', plain,
% 0.20/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.20/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F))),
% 0.20/0.52      inference('demod', [status(thm)], ['118', '155'])).
% 0.20/0.52  thf('157', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('158', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_F)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.20/0.52  thf('159', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['157', '158'])).
% 0.20/0.52  thf('160', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '17'])).
% 0.20/0.52  thf('161', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_C)
% 0.20/0.52          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0)
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 sk_F @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['137', '138', '139', '140', '141', '142', '143'])).
% 0.20/0.52  thf('162', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['160', '161'])).
% 0.20/0.52  thf('163', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('164', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C)
% 0.20/0.52        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.20/0.52      inference('clc', [status(thm)], ['162', '163'])).
% 0.20/0.52  thf('165', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('166', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)
% 0.20/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.20/0.52            (u1_struct_0 @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['164', '165'])).
% 0.20/0.52  thf('167', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '17'])).
% 0.20/0.52  thf('168', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.20/0.52            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['159', '166', '167'])).
% 0.20/0.52  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('170', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.20/0.52            = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['168', '169'])).
% 0.20/0.52  thf('171', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('172', plain,
% 0.20/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ sk_F)
% 0.20/0.52         = (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.20/0.52      inference('clc', [status(thm)], ['170', '171'])).
% 0.20/0.52  thf('173', plain,
% 0.20/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52           (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D)) @ 
% 0.20/0.52          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.20/0.52      inference('demod', [status(thm)], ['156', '172'])).
% 0.20/0.52  thf('174', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('175', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('176', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X1)
% 0.20/0.52          | ~ (v2_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | ((k3_tmap_1 @ X1 @ sk_B @ X0 @ X2 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ X0) @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.52  thf('177', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['175', '176'])).
% 0.20/0.52  thf('178', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('181', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.20/0.52              (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52                 (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ X0)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 0.20/0.52  thf('182', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['174', '181'])).
% 0.20/0.52  thf('183', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.20/0.52         sk_E)
% 0.20/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['108', '109'])).
% 0.20/0.52  thf('184', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('185', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.20/0.52  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('187', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['185', '186'])).
% 0.20/0.52  thf('188', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('189', plain,
% 0.20/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ 
% 0.20/0.52         (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D))
% 0.20/0.52         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ sk_E))),
% 0.20/0.52      inference('clc', [status(thm)], ['187', '188'])).
% 0.20/0.52  thf('190', plain,
% 0.20/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52          (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_D) @ 
% 0.20/0.52           sk_E) @ 
% 0.20/0.52          (k2_tmap_1 @ sk_C @ sk_B @ sk_F @ sk_E))),
% 0.20/0.52      inference('demod', [status(thm)], ['173', '189'])).
% 0.20/0.52  thf('191', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (v2_struct_0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['117', '190'])).
% 0.20/0.52  thf('192', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('193', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['191', '192'])).
% 0.20/0.52  thf('194', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('195', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.20/0.52      inference('clc', [status(thm)], ['193', '194'])).
% 0.20/0.52  thf('196', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('197', plain, ((v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('clc', [status(thm)], ['195', '196'])).
% 0.20/0.52  thf('198', plain, ($false), inference('demod', [status(thm)], ['0', '197'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
