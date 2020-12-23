%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UuasadVt8F

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:04 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  306 (2477 expanded)
%              Number of leaves         :   34 ( 731 expanded)
%              Depth                    :   40
%              Number of atoms          : 4339 (112751 expanded)
%              Number of equality atoms :   66 (3675 expanded)
%              Maximal formula depth    :   31 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t125_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                   => ( ( ( F = G )
                                        & ( F = H ) )
                                     => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                      <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                          & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                     => ( ( ( F = G )
                                          & ( F = H ) )
                                       => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                        <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                            & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    sk_F = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t124_tmap_1,axiom,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ! [H: $i] :
                                  ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                 => ( ( ( F = G )
                                      & ( F = H ) )
                                   => ( ( r1_tmap_1 @ ( k1_tsep_1 @ A @ D @ E ) @ B @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ F )
                                    <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                        & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X21 )
      | ( r1_tmap_1 @ X19 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X19 ) @ X25 )
      | ( X21 != X23 )
      | ( X21 != X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X19 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X19 ) @ X23 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','34','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X17 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('66',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 @ ( k3_tmap_1 @ X30 @ X27 @ X29 @ X29 @ X28 ) )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('80',plain,(
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

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('97',plain,(
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

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C )
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','125'])).

thf('127',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('129',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('132',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['10','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('140',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['134','137','140','141'])).

thf('143',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('144',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X21 )
      | ( r1_tmap_1 @ X22 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X22 ) @ X23 )
      | ( X21 != X23 )
      | ( X21 != X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('147',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X22 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X22 ) @ X23 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','155'])).

thf('157',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160'])).

thf('162',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['143','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('166',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('167',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('171',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['168','172'])).

thf('174',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['142','175'])).

thf('177',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('187',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['185','186'])).

thf('188',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['6','187'])).

thf('189',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('190',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','132'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('197',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('198',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('201',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('202',plain,
    ( ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['199','202'])).

thf('204',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['192'])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['192'])).

thf('215',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['215'])).

thf('217',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['214','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('221',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['215'])).

thf('222',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('223',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['192'])).

thf('234',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['213','219','232','233'])).

thf('235',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['189','234'])).

thf('236',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ X19 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X19 ) @ X25 )
      | ~ ( r1_tmap_1 @ X22 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X22 ) @ X23 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X21 )
      | ( X21 != X23 )
      | ( X21 != X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('238',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) @ X23 )
      | ~ ( r1_tmap_1 @ X22 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X22 ) @ X23 )
      | ~ ( r1_tmap_1 @ X19 @ X18 @ ( k2_tmap_1 @ X20 @ X18 @ X24 @ X19 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ ( k1_tsep_1 @ X20 @ X19 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['236','238'])).

thf('240',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['239','240','241','242','243','244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','246'])).

thf('248',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
    | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ sk_G )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['188','250'])).

thf('252',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('254',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('255',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('258',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['251','252','253','254','255','256','257','258'])).

thf('260',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('261',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['185'])).

thf('262',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['259','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,(
    $false ),
    inference(demod,[status(thm)],['0','269'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UuasadVt8F
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 306 iterations in 0.255s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.73  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.55/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(sk_G_type, type, sk_G: $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(sk_H_type, type, sk_H: $i).
% 0.55/0.73  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.55/0.73  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.55/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.73  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.73  thf(t125_tmap_1, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73             ( l1_pre_topc @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                 ( m1_subset_1 @
% 0.55/0.73                   C @ 
% 0.55/0.73                   ( k1_zfmisc_1 @
% 0.55/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                   ( ![E:$i]:
% 0.55/0.73                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.55/0.73                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.55/0.73                         ( ![F:$i]:
% 0.55/0.73                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73                             ( ![G:$i]:
% 0.55/0.73                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.73                                 ( ![H:$i]:
% 0.55/0.73                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.55/0.73                                     ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.55/0.73                                       ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.55/0.73                                         ( ( r1_tmap_1 @
% 0.55/0.73                                             D @ B @ 
% 0.55/0.73                                             ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.55/0.73                                           ( r1_tmap_1 @
% 0.55/0.73                                             E @ B @ 
% 0.55/0.73                                             ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.73            ( l1_pre_topc @ A ) ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73                ( l1_pre_topc @ B ) ) =>
% 0.55/0.73              ( ![C:$i]:
% 0.55/0.73                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.73                    ( v1_funct_2 @
% 0.55/0.73                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                    ( m1_subset_1 @
% 0.55/0.73                      C @ 
% 0.55/0.73                      ( k1_zfmisc_1 @
% 0.55/0.73                        ( k2_zfmisc_1 @
% 0.55/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73                  ( ![D:$i]:
% 0.55/0.73                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                      ( ![E:$i]:
% 0.55/0.73                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.55/0.73                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.55/0.73                            ( ![F:$i]:
% 0.55/0.73                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73                                ( ![G:$i]:
% 0.55/0.73                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.73                                    ( ![H:$i]:
% 0.55/0.73                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.55/0.73                                        ( ( ( ( F ) = ( G ) ) & 
% 0.55/0.73                                            ( ( F ) = ( H ) ) ) =>
% 0.55/0.73                                          ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.55/0.73                                            ( ( r1_tmap_1 @
% 0.55/0.73                                                D @ B @ 
% 0.55/0.73                                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.55/0.73                                                G ) & 
% 0.55/0.73                                              ( r1_tmap_1 @
% 0.55/0.73                                                E @ B @ 
% 0.55/0.73                                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.55/0.73                                                H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t125_tmap_1])).
% 0.55/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.73         sk_H)
% 0.55/0.73        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.73         sk_H))
% 0.55/0.73         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.73               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.73      inference('split', [status(esa)], ['1'])).
% 0.55/0.73  thf('3', plain, (((sk_F) = (sk_H))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('4', plain, (((sk_F) = (sk_G))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('5', plain, (((sk_H) = (sk_G))),
% 0.55/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.73         sk_G))
% 0.55/0.73         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.73               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.73      inference('demod', [status(thm)], ['2', '5'])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.73         sk_G)
% 0.55/0.73        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.55/0.73         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.73      inference('split', [status(esa)], ['7'])).
% 0.55/0.73  thf('9', plain, (((sk_F) = (sk_G))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.73         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.73  thf('11', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t124_tmap_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73             ( l1_pre_topc @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                 ( m1_subset_1 @
% 0.55/0.73                   C @ 
% 0.55/0.73                   ( k1_zfmisc_1 @
% 0.55/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                   ( ![E:$i]:
% 0.55/0.73                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.55/0.73                       ( ![F:$i]:
% 0.55/0.73                         ( ( m1_subset_1 @
% 0.55/0.73                             F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) ) =>
% 0.55/0.74                           ( ![G:$i]:
% 0.55/0.74                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.74                               ( ![H:$i]:
% 0.55/0.74                                 ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.55/0.74                                   ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.55/0.74                                     ( ( r1_tmap_1 @
% 0.55/0.74                                         ( k1_tsep_1 @ A @ D @ E ) @ B @ 
% 0.55/0.74                                         ( k2_tmap_1 @
% 0.55/0.74                                           A @ B @ C @ 
% 0.55/0.74                                           ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 0.55/0.74                                         F ) <=>
% 0.55/0.74                                       ( ( r1_tmap_1 @
% 0.55/0.74                                           D @ B @ 
% 0.55/0.74                                           ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.55/0.74                                         ( r1_tmap_1 @
% 0.55/0.74                                           E @ B @ 
% 0.55/0.74                                           ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 0.55/0.74         X25 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X21 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74               (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74               X21)
% 0.55/0.74          | (r1_tmap_1 @ X19 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X19) @ X25)
% 0.55/0.74          | ((X21) != (X23))
% 0.55/0.74          | ((X21) != (X25))
% 0.55/0.74          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X19))
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | (v2_struct_0 @ X20))),
% 0.55/0.74      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.55/0.74          | (r1_tmap_1 @ X19 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X19) @ X23)
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74               (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74               X23)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X18))),
% 0.55/0.74      inference('simplify', [status(thm)], ['13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['12', '14'])).
% 0.55/0.74  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['15', '16', '17', '18', '19', '20', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.55/0.74             X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['11', '22'])).
% 0.55/0.74  thf('24', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('25', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('26', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('27', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_k2_tmap_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.55/0.74         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74         ( m1_subset_1 @
% 0.55/0.74           C @ 
% 0.55/0.74           ( k1_zfmisc_1 @
% 0.55/0.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.55/0.74         ( l1_struct_0 @ D ) ) =>
% 0.55/0.74       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.55/0.74         ( v1_funct_2 @
% 0.55/0.74           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.55/0.74           ( u1_struct_0 @ B ) ) & 
% 0.55/0.74         ( m1_subset_1 @
% 0.55/0.74           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.55/0.74           ( k1_zfmisc_1 @
% 0.55/0.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X14 @ 
% 0.55/0.74             (k1_zfmisc_1 @ 
% 0.55/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_struct_0 @ X16)
% 0.55/0.74          | ~ (l1_struct_0 @ X15)
% 0.55/0.74          | ~ (l1_struct_0 @ X17)
% 0.55/0.74          | (v1_funct_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17)))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_A)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.74  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_l1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.74  thf('33', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('36', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['31', '34', '37', '38', '39'])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X14 @ 
% 0.55/0.74             (k1_zfmisc_1 @ 
% 0.55/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_struct_0 @ X16)
% 0.55/0.74          | ~ (l1_struct_0 @ X15)
% 0.55/0.74          | ~ (l1_struct_0 @ X17)
% 0.55/0.74          | (v1_funct_2 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.55/0.74             (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_A)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X14 @ 
% 0.55/0.74             (k1_zfmisc_1 @ 
% 0.55/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_struct_0 @ X16)
% 0.55/0.74          | ~ (l1_struct_0 @ X15)
% 0.55/0.74          | ~ (l1_struct_0 @ X17)
% 0.55/0.74          | (m1_subset_1 @ (k2_tmap_1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.55/0.74             (k1_zfmisc_1 @ 
% 0.55/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16)))))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_A)
% 0.55/0.74          | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.55/0.74  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('56', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_r2_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.74         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.74       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.74  thf('58', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.55/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X3)
% 0.55/0.74          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.55/0.74          | ((X0) = (X3))
% 0.55/0.74          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             X0)
% 0.55/0.74          | ((sk_C) = (X0))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             X0)
% 0.55/0.74          | ((sk_C) = (X0))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.74        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.55/0.74             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['56', '62'])).
% 0.55/0.74  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('65', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.55/0.74             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['63', '64'])).
% 0.55/0.74  thf(t2_tsep_1, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.74  thf('67', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t74_tmap_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( ( v1_funct_1 @ D ) & 
% 0.55/0.74                     ( v1_funct_2 @
% 0.55/0.74                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                     ( m1_subset_1 @
% 0.55/0.74                       D @ 
% 0.55/0.74                       ( k1_zfmisc_1 @
% 0.55/0.74                         ( k2_zfmisc_1 @
% 0.55/0.74                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                   ( r2_funct_2 @
% 0.55/0.74                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.55/0.74                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('68', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X27)
% 0.55/0.74          | ~ (v2_pre_topc @ X27)
% 0.55/0.74          | ~ (l1_pre_topc @ X27)
% 0.55/0.74          | ~ (v1_funct_1 @ X28)
% 0.55/0.74          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 0.55/0.74          | (r2_funct_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28 @ 
% 0.55/0.74             (k3_tmap_1 @ X30 @ X27 @ X29 @ X29 @ X28))
% 0.55/0.74          | ~ (m1_pre_topc @ X29 @ X30)
% 0.55/0.74          | (v2_struct_0 @ X29)
% 0.55/0.74          | ~ (l1_pre_topc @ X30)
% 0.55/0.74          | ~ (v2_pre_topc @ X30)
% 0.55/0.74          | (v2_struct_0 @ X30))),
% 0.55/0.74      inference('cnf', [status(esa)], [t74_tmap_1])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.55/0.74          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.55/0.74  thf('70', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('74', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.55/0.74          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.55/0.74  thf('75', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_B)
% 0.55/0.74        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C))
% 0.55/0.74        | (v2_struct_0 @ sk_A)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['66', '74'])).
% 0.55/0.74  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('77', plain,
% 0.55/0.74      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.74  thf('78', plain,
% 0.55/0.74      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.74  thf('79', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d5_tmap_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_pre_topc @ C @ A ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( m1_pre_topc @ D @ A ) =>
% 0.55/0.74                   ( ![E:$i]:
% 0.55/0.74                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.74                         ( v1_funct_2 @
% 0.55/0.74                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                         ( m1_subset_1 @
% 0.55/0.74                           E @ 
% 0.55/0.74                           ( k1_zfmisc_1 @
% 0.55/0.74                             ( k2_zfmisc_1 @
% 0.55/0.74                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                       ( ( m1_pre_topc @ D @ C ) =>
% 0.55/0.74                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.55/0.74                           ( k2_partfun1 @
% 0.55/0.74                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.55/0.74                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('80', plain,
% 0.55/0.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X9)
% 0.55/0.74          | ~ (v2_pre_topc @ X9)
% 0.55/0.74          | ~ (l1_pre_topc @ X9)
% 0.55/0.74          | ~ (m1_pre_topc @ X10 @ X11)
% 0.55/0.74          | ~ (m1_pre_topc @ X10 @ X12)
% 0.55/0.74          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.55/0.74                 X13 @ (u1_struct_0 @ X10)))
% 0.55/0.74          | ~ (m1_subset_1 @ X13 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.55/0.74          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.55/0.74          | ~ (v1_funct_1 @ X13)
% 0.55/0.74          | ~ (m1_pre_topc @ X12 @ X11)
% 0.55/0.74          | ~ (l1_pre_topc @ X11)
% 0.55/0.74          | ~ (v2_pre_topc @ X11)
% 0.55/0.74          | (v2_struct_0 @ X11))),
% 0.55/0.74      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.55/0.74  thf('81', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X1)))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.74  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('83', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('86', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.55/0.74          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X1)))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.55/0.74  thf('87', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['78', '86'])).
% 0.55/0.74  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('91', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X0)))
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.55/0.74  thf('92', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('simplify', [status(thm)], ['91'])).
% 0.55/0.74  thf('93', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_B)
% 0.55/0.74        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.55/0.74            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74               sk_C @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['77', '92'])).
% 0.55/0.74  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('95', plain,
% 0.55/0.74      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.74  thf('96', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d4_tmap_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                 ( m1_subset_1 @
% 0.55/0.74                   C @ 
% 0.55/0.74                   ( k1_zfmisc_1 @
% 0.55/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( m1_pre_topc @ D @ A ) =>
% 0.55/0.74                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.55/0.74                     ( k2_partfun1 @
% 0.55/0.74                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.55/0.74                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('97', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X5)
% 0.55/0.74          | ~ (v2_pre_topc @ X5)
% 0.55/0.74          | ~ (l1_pre_topc @ X5)
% 0.55/0.74          | ~ (m1_pre_topc @ X6 @ X7)
% 0.55/0.74          | ((k2_tmap_1 @ X7 @ X5 @ X8 @ X6)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X8 @ 
% 0.55/0.74                 (u1_struct_0 @ X6)))
% 0.55/0.74          | ~ (m1_subset_1 @ X8 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.55/0.74          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.55/0.74          | ~ (v1_funct_1 @ X8)
% 0.55/0.74          | ~ (l1_pre_topc @ X7)
% 0.55/0.74          | ~ (v2_pre_topc @ X7)
% 0.55/0.74          | (v2_struct_0 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.55/0.74  thf('98', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['96', '97'])).
% 0.55/0.74  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('102', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('105', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.55/0.74              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74                 sk_C @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['98', '99', '100', '101', '102', '103', '104'])).
% 0.55/0.74  thf('106', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_B)
% 0.55/0.74        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.55/0.74            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74               sk_C @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['95', '105'])).
% 0.55/0.74  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('108', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.55/0.74            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74               sk_C @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['106', '107'])).
% 0.55/0.74  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('110', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.55/0.74            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74               sk_C @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('clc', [status(thm)], ['108', '109'])).
% 0.55/0.74  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('112', plain,
% 0.55/0.74      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.55/0.74         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74            (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('clc', [status(thm)], ['110', '111'])).
% 0.55/0.74  thf('113', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.55/0.74            = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['93', '94', '112'])).
% 0.55/0.74  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('115', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.55/0.74            = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('clc', [status(thm)], ['113', '114'])).
% 0.55/0.74  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('117', plain,
% 0.55/0.74      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_C)
% 0.55/0.74         = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.55/0.74      inference('clc', [status(thm)], ['115', '116'])).
% 0.55/0.74  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('120', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | (v2_struct_0 @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['75', '76', '117', '118', '119'])).
% 0.55/0.74  thf('121', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('simplify', [status(thm)], ['120'])).
% 0.55/0.74  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('123', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('clc', [status(thm)], ['121', '122'])).
% 0.55/0.74  thf('124', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('125', plain,
% 0.55/0.74      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74        (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.55/0.74      inference('clc', [status(thm)], ['123', '124'])).
% 0.55/0.74  thf('126', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 0.55/0.74             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['65', '125'])).
% 0.55/0.74  thf('127', plain,
% 0.55/0.74      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.74        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['48', '126'])).
% 0.55/0.74  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('129', plain,
% 0.55/0.74      ((((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 0.55/0.74        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['127', '128'])).
% 0.55/0.74  thf('130', plain,
% 0.55/0.74      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.74        | ((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['40', '129'])).
% 0.55/0.74  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('132', plain, (((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['130', '131'])).
% 0.55/0.74  thf('133', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['28', '132'])).
% 0.55/0.74  thf('134', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.55/0.74         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['10', '133'])).
% 0.55/0.74  thf('135', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('136', plain, (((sk_F) = (sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('137', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['135', '136'])).
% 0.55/0.74  thf('138', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('139', plain, (((sk_H) = (sk_G))),
% 0.55/0.74      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf('140', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.55/0.74      inference('demod', [status(thm)], ['138', '139'])).
% 0.55/0.74  thf('141', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('142', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['134', '137', '140', '141'])).
% 0.55/0.74  thf('143', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('144', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('145', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('146', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 0.55/0.74         X25 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X21 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74               (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74               X21)
% 0.55/0.74          | (r1_tmap_1 @ X22 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X22) @ X23)
% 0.55/0.74          | ((X21) != (X23))
% 0.55/0.74          | ((X21) != (X25))
% 0.55/0.74          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X19))
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | (v2_struct_0 @ X20))),
% 0.55/0.74      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.55/0.74  thf('147', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.55/0.74          | (r1_tmap_1 @ X22 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X22) @ X23)
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74               (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74               X23)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X18))),
% 0.55/0.74      inference('simplify', [status(thm)], ['146'])).
% 0.55/0.74  thf('148', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['145', '147'])).
% 0.55/0.74  thf('149', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('150', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('151', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('155', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['148', '149', '150', '151', '152', '153', '154'])).
% 0.55/0.74  thf('156', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.55/0.74             X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['144', '155'])).
% 0.55/0.74  thf('157', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('158', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('159', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('160', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('161', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['156', '157', '158', '159', '160'])).
% 0.55/0.74  thf('162', plain, (((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['130', '131'])).
% 0.55/0.74  thf('163', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['161', '162'])).
% 0.55/0.74  thf('164', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.55/0.74         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['143', '163'])).
% 0.55/0.74  thf('165', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['135', '136'])).
% 0.55/0.74  thf('166', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.55/0.74      inference('demod', [status(thm)], ['138', '139'])).
% 0.55/0.74  thf('167', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('168', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.55/0.74  thf('169', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_H)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('170', plain, (((sk_H) = (sk_G))),
% 0.55/0.74      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf('171', plain, (((sk_F) = (sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('172', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.55/0.74      inference('demod', [status(thm)], ['169', '170', '171'])).
% 0.55/0.74  thf('173', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)
% 0.55/0.74         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.55/0.74         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['168', '172'])).
% 0.55/0.74  thf('174', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('175', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)
% 0.55/0.74         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['173', '174'])).
% 0.55/0.74  thf('176', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['142', '175'])).
% 0.55/0.74  thf('177', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['176'])).
% 0.55/0.74  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('179', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['177', '178'])).
% 0.55/0.74  thf('180', plain, (~ (v2_struct_0 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('181', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('clc', [status(thm)], ['179', '180'])).
% 0.55/0.74  thf('182', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('183', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D)) <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('clc', [status(thm)], ['181', '182'])).
% 0.55/0.74  thf('184', plain, (~ (v2_struct_0 @ sk_D)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('185', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('sup-', [status(thm)], ['183', '184'])).
% 0.55/0.74  thf('186', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74         sk_H)) | 
% 0.55/0.74       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('split', [status(esa)], ['1'])).
% 0.55/0.74  thf('187', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74         sk_H))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['185', '186'])).
% 0.55/0.74  thf('188', plain,
% 0.55/0.74      ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74        sk_G)),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['6', '187'])).
% 0.55/0.74  thf('189', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74         sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['7'])).
% 0.55/0.74  thf('190', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74         sk_G)
% 0.55/0.74        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('191', plain, (((sk_F) = (sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('192', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74         sk_G)
% 0.55/0.74        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.55/0.74      inference('demod', [status(thm)], ['190', '191'])).
% 0.55/0.74  thf('193', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['192'])).
% 0.55/0.74  thf('194', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_E)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['28', '132'])).
% 0.55/0.74  thf('195', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.55/0.74         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['193', '194'])).
% 0.55/0.74  thf('196', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['135', '136'])).
% 0.55/0.74  thf('197', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.55/0.74      inference('demod', [status(thm)], ['138', '139'])).
% 0.55/0.74  thf('198', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('199', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.55/0.74  thf('200', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74         sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('demod', [status(thm)], ['2', '5'])).
% 0.55/0.74  thf('201', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.55/0.74      inference('demod', [status(thm)], ['169', '170', '171'])).
% 0.55/0.74  thf('202', plain,
% 0.55/0.74      (((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.55/0.74         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['200', '201'])).
% 0.55/0.74  thf('203', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)
% 0.55/0.74         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['199', '202'])).
% 0.55/0.74  thf('204', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['192'])).
% 0.55/0.74  thf('205', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('demod', [status(thm)], ['203', '204'])).
% 0.55/0.74  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('207', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['205', '206'])).
% 0.55/0.74  thf('208', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('209', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('clc', [status(thm)], ['207', '208'])).
% 0.55/0.74  thf('210', plain, (~ (v2_struct_0 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('211', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('clc', [status(thm)], ['209', '210'])).
% 0.55/0.74  thf('212', plain, (~ (v2_struct_0 @ sk_D)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('213', plain,
% 0.55/0.74      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.55/0.74       ~
% 0.55/0.74       ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74         sk_H))),
% 0.55/0.74      inference('sup-', [status(thm)], ['211', '212'])).
% 0.55/0.74  thf('214', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['192'])).
% 0.55/0.74  thf('215', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_H)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('216', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('split', [status(esa)], ['215'])).
% 0.55/0.74  thf('217', plain, (((sk_F) = (sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('218', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['216', '217'])).
% 0.55/0.74  thf('219', plain,
% 0.55/0.74      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.55/0.74       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('sup-', [status(thm)], ['214', '218'])).
% 0.55/0.74  thf('220', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.55/0.74  thf('221', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_H))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('split', [status(esa)], ['215'])).
% 0.55/0.74  thf('222', plain, (((sk_H) = (sk_G))),
% 0.55/0.74      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf('223', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74           sk_G))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('demod', [status(thm)], ['221', '222'])).
% 0.55/0.74  thf('224', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_E)
% 0.55/0.74         | (v2_struct_0 @ sk_D)
% 0.55/0.74         | (v2_struct_0 @ sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['220', '223'])).
% 0.55/0.74  thf('225', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('226', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['224', '225'])).
% 0.55/0.74  thf('227', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('228', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('clc', [status(thm)], ['226', '227'])).
% 0.55/0.74  thf('229', plain, (~ (v2_struct_0 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('230', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.55/0.74               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('clc', [status(thm)], ['228', '229'])).
% 0.55/0.74  thf('231', plain, (~ (v2_struct_0 @ sk_D)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('232', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.55/0.74         sk_H)) | 
% 0.55/0.74       ~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('sup-', [status(thm)], ['230', '231'])).
% 0.55/0.74  thf('233', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74         sk_G)) | 
% 0.55/0.74       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.55/0.74      inference('split', [status(esa)], ['192'])).
% 0.55/0.74  thf('234', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74         sk_G))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['213', '219', '232', '233'])).
% 0.55/0.74  thf('235', plain,
% 0.55/0.74      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.55/0.74        sk_G)),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['189', '234'])).
% 0.55/0.74  thf('236', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('237', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 0.55/0.74         X25 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X21 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (r1_tmap_1 @ X19 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X19) @ 
% 0.55/0.74               X25)
% 0.55/0.74          | ~ (r1_tmap_1 @ X22 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X22) @ 
% 0.55/0.74               X23)
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74             (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74             X21)
% 0.55/0.74          | ((X21) != (X23))
% 0.55/0.74          | ((X21) != (X25))
% 0.55/0.74          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X19))
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | (v2_struct_0 @ X20))),
% 0.55/0.74      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.55/0.74  thf('238', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X20)
% 0.55/0.74          | ~ (v2_pre_topc @ X20)
% 0.55/0.74          | ~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.55/0.74          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.55/0.74          | (v2_struct_0 @ X22)
% 0.55/0.74          | ~ (m1_pre_topc @ X22 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ X20 @ X19 @ X22) @ X18 @ 
% 0.55/0.74             (k2_tmap_1 @ X20 @ X18 @ X24 @ (k1_tsep_1 @ X20 @ X19 @ X22)) @ 
% 0.55/0.74             X23)
% 0.55/0.74          | ~ (r1_tmap_1 @ X22 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X22) @ 
% 0.55/0.74               X23)
% 0.55/0.74          | ~ (r1_tmap_1 @ X19 @ X18 @ (k2_tmap_1 @ X20 @ X18 @ X24 @ X19) @ 
% 0.55/0.74               X23)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ X20 @ X19 @ X22)))
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.74          | (v2_struct_0 @ X19)
% 0.55/0.74          | ~ (l1_pre_topc @ X18)
% 0.55/0.74          | ~ (v2_pre_topc @ X18)
% 0.55/0.74          | (v2_struct_0 @ X18))),
% 0.55/0.74      inference('simplify', [status(thm)], ['237'])).
% 0.55/0.74  thf('239', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74             X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['236', '238'])).
% 0.55/0.74  thf('240', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('241', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('242', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('246', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.55/0.74               X2)
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.55/0.74             X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['239', '240', '241', '242', '243', '244', '245'])).
% 0.55/0.74  thf('247', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.55/0.74             sk_G)
% 0.55/0.74          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74               sk_G)
% 0.55/0.74          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_subset_1 @ sk_G @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['235', '246'])).
% 0.55/0.74  thf('248', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('249', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('250', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.55/0.74             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.55/0.74             sk_G)
% 0.55/0.74          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.55/0.74               sk_G)
% 0.55/0.74          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_subset_1 @ sk_G @ 
% 0.55/0.74               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.55/0.74          | (v2_struct_0 @ sk_D)
% 0.55/0.74          | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['247', '248', '249'])).
% 0.55/0.74  thf('251', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | (v2_struct_0 @ sk_D)
% 0.55/0.74        | ~ (m1_subset_1 @ sk_G @ 
% 0.55/0.74             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.55/0.74        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.55/0.74        | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B @ 
% 0.55/0.74           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.55/0.74           sk_G)
% 0.55/0.74        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_E)
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['188', '250'])).
% 0.55/0.74  thf('252', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('253', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['135', '136'])).
% 0.55/0.74  thf('254', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.55/0.74      inference('demod', [status(thm)], ['138', '139'])).
% 0.55/0.74  thf('255', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('256', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('257', plain, (((sk_C) = (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['130', '131'])).
% 0.55/0.74  thf('258', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('259', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | (v2_struct_0 @ sk_D)
% 0.55/0.74        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.55/0.74        | (v2_struct_0 @ sk_E)
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['251', '252', '253', '254', '255', '256', '257', '258'])).
% 0.55/0.74  thf('260', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.55/0.74      inference('demod', [status(thm)], ['216', '217'])).
% 0.55/0.74  thf('261', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['185'])).
% 0.55/0.74  thf('262', plain, (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['260', '261'])).
% 0.55/0.74  thf('263', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_E)
% 0.55/0.74        | (v2_struct_0 @ sk_D)
% 0.55/0.74        | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['259', '262'])).
% 0.55/0.74  thf('264', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('265', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.55/0.74      inference('sup-', [status(thm)], ['263', '264'])).
% 0.55/0.74  thf('266', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('267', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.55/0.74      inference('clc', [status(thm)], ['265', '266'])).
% 0.55/0.74  thf('268', plain, (~ (v2_struct_0 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('269', plain, ((v2_struct_0 @ sk_D)),
% 0.55/0.74      inference('clc', [status(thm)], ['267', '268'])).
% 0.55/0.74  thf('270', plain, ($false), inference('demod', [status(thm)], ['0', '269'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
