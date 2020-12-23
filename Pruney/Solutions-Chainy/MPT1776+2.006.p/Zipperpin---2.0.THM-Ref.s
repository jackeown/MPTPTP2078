%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LFFlx6eAqW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:24 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 888 expanded)
%              Number of leaves         :   33 ( 263 expanded)
%              Depth                    :   28
%              Number of atoms          : 2389 (34071 expanded)
%              Number of equality atoms :   34 ( 478 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t87_tmap_1,conjecture,(
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
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( v1_tsep_1 @ C @ B )
                            & ( m1_pre_topc @ C @ B )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
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

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
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

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','43','48','49','50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['4'])).

thf('66',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tmap_1,axiom,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X39 )
      | ( X39 != X36 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('71',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X34 @ X37 @ X38 @ X36 )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ ( k2_tmap_1 @ X34 @ X37 @ X38 @ X35 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_tsep_1 @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('85',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('88',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('94',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','87'])).

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

thf('102',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('103',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v3_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('110',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('111',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['108','117'])).

thf('119',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['95','118'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['80','81','82','83','119'])).

thf('121',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('130',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['14','18','128','129'])).

thf('131',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['5','130'])).

thf('132',plain,(
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

thf('133',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ( X33 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('134',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X30 )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
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
    inference('sup-',[status(thm)],['132','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('137',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('138',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['131','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','145'])).

thf('147',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('150',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('151',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('153',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('154',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['14','18','128','154'])).

thf('156',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['151','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['148','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['0','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LFFlx6eAqW
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:41:19 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 100 iterations in 0.053s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.25/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.55  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.25/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.25/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.25/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.25/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.25/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.25/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.25/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.25/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.55  thf(t87_tmap_1, conjecture,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.55                   ( ![E:$i]:
% 0.25/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.55                         ( v1_funct_2 @
% 0.25/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.55                         ( m1_subset_1 @
% 0.25/0.55                           E @ 
% 0.25/0.55                           ( k1_zfmisc_1 @
% 0.25/0.55                             ( k2_zfmisc_1 @
% 0.25/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.55                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.25/0.55                           ( m1_pre_topc @ C @ D ) ) =>
% 0.25/0.55                         ( ![F:$i]:
% 0.25/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.55                             ( ![G:$i]:
% 0.25/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.55                                 ( ( ( F ) = ( G ) ) =>
% 0.25/0.55                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.25/0.55                                     ( r1_tmap_1 @
% 0.25/0.55                                       C @ A @ 
% 0.25/0.55                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i]:
% 0.25/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.55            ( l1_pre_topc @ A ) ) =>
% 0.25/0.55          ( ![B:$i]:
% 0.25/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55                ( l1_pre_topc @ B ) ) =>
% 0.25/0.55              ( ![C:$i]:
% 0.25/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.55                  ( ![D:$i]:
% 0.25/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.55                      ( ![E:$i]:
% 0.25/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.55                            ( v1_funct_2 @
% 0.25/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.55                            ( m1_subset_1 @
% 0.25/0.55                              E @ 
% 0.25/0.55                              ( k1_zfmisc_1 @
% 0.25/0.55                                ( k2_zfmisc_1 @
% 0.25/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.55                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.25/0.55                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.25/0.55                            ( ![F:$i]:
% 0.25/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.55                                ( ![G:$i]:
% 0.25/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.55                                    ( ( ( F ) = ( G ) ) =>
% 0.25/0.55                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.25/0.55                                        ( r1_tmap_1 @
% 0.25/0.55                                          C @ A @ 
% 0.25/0.55                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.25/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('2', plain, (((sk_F) = (sk_G))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.25/0.55  thf('4', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.25/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('5', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.25/0.55      inference('split', [status(esa)], ['4'])).
% 0.25/0.55  thf('6', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.25/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('7', plain, (((sk_F) = (sk_G))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('8', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.25/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.25/0.55      inference('split', [status(esa)], ['8'])).
% 0.25/0.55  thf('10', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.25/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('11', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.25/0.55         <= (~
% 0.25/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('split', [status(esa)], ['10'])).
% 0.25/0.55  thf('12', plain, (((sk_F) = (sk_G))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('13', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.25/0.55         <= (~
% 0.25/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.25/0.55  thf('14', plain,
% 0.25/0.55      (~
% 0.25/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.25/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.25/0.55      inference('sup-', [status(thm)], ['9', '13'])).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.25/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('16', plain, (((sk_F) = (sk_G))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('17', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.25/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.55  thf('18', plain,
% 0.25/0.55      (~
% 0.25/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.25/0.55       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('split', [status(esa)], ['17'])).
% 0.25/0.55  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('21', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_E @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(d5_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.25/0.55                   ( ![E:$i]:
% 0.25/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.55                         ( v1_funct_2 @
% 0.25/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.55                         ( m1_subset_1 @
% 0.25/0.55                           E @ 
% 0.25/0.55                           ( k1_zfmisc_1 @
% 0.25/0.55                             ( k2_zfmisc_1 @
% 0.25/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.55                       ( ( m1_pre_topc @ D @ C ) =>
% 0.25/0.55                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.25/0.55                           ( k2_partfun1 @
% 0.25/0.55                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.25/0.55                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X18)
% 0.25/0.55          | ~ (v2_pre_topc @ X18)
% 0.25/0.55          | ~ (l1_pre_topc @ X18)
% 0.25/0.55          | ~ (m1_pre_topc @ X19 @ X20)
% 0.25/0.55          | ~ (m1_pre_topc @ X19 @ X21)
% 0.25/0.55          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.25/0.55                 X22 @ (u1_struct_0 @ X19)))
% 0.25/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 0.25/0.55          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 0.25/0.55          | ~ (v1_funct_1 @ X22)
% 0.25/0.55          | ~ (m1_pre_topc @ X21 @ X20)
% 0.25/0.55          | ~ (l1_pre_topc @ X20)
% 0.25/0.55          | ~ (v2_pre_topc @ X20)
% 0.25/0.55          | (v2_struct_0 @ X20))),
% 0.25/0.55      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.25/0.55  thf('23', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X0)
% 0.25/0.55          | ~ (v2_pre_topc @ X0)
% 0.25/0.55          | ~ (l1_pre_topc @ X0)
% 0.25/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.55          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.25/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.55  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('25', plain,
% 0.25/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('28', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X0)
% 0.25/0.55          | ~ (v2_pre_topc @ X0)
% 0.25/0.55          | ~ (l1_pre_topc @ X0)
% 0.25/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.55          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.25/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.25/0.55  thf('29', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_A)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.55          | (v2_struct_0 @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['20', '28'])).
% 0.25/0.55  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('32', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_A)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.55          | (v2_struct_0 @ sk_B))),
% 0.25/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.25/0.55  thf('33', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_B)
% 0.25/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.25/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.25/0.55        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.25/0.55        | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['19', '32'])).
% 0.25/0.55  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('35', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_E @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(d4_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.55                 ( m1_subset_1 @
% 0.25/0.55                   C @ 
% 0.25/0.55                   ( k1_zfmisc_1 @
% 0.25/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.25/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.25/0.55                     ( k2_partfun1 @
% 0.25/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.25/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('36', plain,
% 0.25/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X14)
% 0.25/0.55          | ~ (v2_pre_topc @ X14)
% 0.25/0.55          | ~ (l1_pre_topc @ X14)
% 0.25/0.55          | ~ (m1_pre_topc @ X15 @ X16)
% 0.25/0.55          | ((k2_tmap_1 @ X16 @ X14 @ X17 @ X15)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14) @ 
% 0.25/0.55                 X17 @ (u1_struct_0 @ X15)))
% 0.25/0.55          | ~ (m1_subset_1 @ X17 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))))
% 0.25/0.55          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X14))
% 0.25/0.55          | ~ (v1_funct_1 @ X17)
% 0.25/0.55          | ~ (l1_pre_topc @ X16)
% 0.25/0.55          | ~ (v2_pre_topc @ X16)
% 0.25/0.55          | (v2_struct_0 @ X16))),
% 0.25/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.25/0.55  thf('37', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_D)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.25/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.55          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.25/0.55  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(cc1_pre_topc, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.25/0.55  thf('39', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X0 @ X1)
% 0.25/0.55          | (v2_pre_topc @ X0)
% 0.25/0.55          | ~ (l1_pre_topc @ X1)
% 0.25/0.55          | ~ (v2_pre_topc @ X1))),
% 0.25/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.25/0.55  thf('40', plain,
% 0.25/0.55      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.25/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.25/0.55  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('43', plain, ((v2_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.25/0.55  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(dt_m1_pre_topc, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.25/0.55  thf('45', plain,
% 0.25/0.55      (![X2 : $i, X3 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.25/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.25/0.55  thf('46', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.25/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.55  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.55  thf('49', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('50', plain,
% 0.25/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('53', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_D)
% 0.25/0.55          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)],
% 0.25/0.55                ['37', '43', '48', '49', '50', '51', '52'])).
% 0.25/0.55  thf('54', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.25/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.25/0.55        | (v2_struct_0 @ sk_D))),
% 0.25/0.55      inference('sup-', [status(thm)], ['34', '53'])).
% 0.25/0.55  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('56', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_D)
% 0.25/0.55        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.25/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.25/0.55      inference('clc', [status(thm)], ['54', '55'])).
% 0.25/0.55  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('58', plain,
% 0.25/0.55      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.25/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.25/0.55            (u1_struct_0 @ sk_C)))),
% 0.25/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.25/0.55  thf('59', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('60', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_B)
% 0.25/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.25/0.55            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.25/0.55        | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['33', '58', '59'])).
% 0.25/0.55  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('62', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.25/0.55            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.25/0.55      inference('clc', [status(thm)], ['60', '61'])).
% 0.25/0.55  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('64', plain,
% 0.25/0.55      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.25/0.55         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.25/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.25/0.55  thf('65', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('split', [status(esa)], ['4'])).
% 0.25/0.55  thf('66', plain, (((sk_F) = (sk_G))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('67', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.25/0.55  thf('68', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.25/0.55         sk_F))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('sup+', [status(thm)], ['64', '67'])).
% 0.25/0.55  thf('69', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_E @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t67_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.55                 ( m1_subset_1 @
% 0.25/0.55                   C @ 
% 0.25/0.55                   ( k1_zfmisc_1 @
% 0.25/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.25/0.55                     ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.55                   ( ![E:$i]:
% 0.25/0.55                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.25/0.55                       ( ![F:$i]:
% 0.25/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.55                           ( ( ( E ) = ( F ) ) =>
% 0.25/0.55                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.25/0.55                               ( r1_tmap_1 @
% 0.25/0.55                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('70', plain,
% 0.25/0.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X34)
% 0.25/0.55          | ~ (v2_pre_topc @ X34)
% 0.25/0.55          | ~ (l1_pre_topc @ X34)
% 0.25/0.55          | (v2_struct_0 @ X35)
% 0.25/0.55          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.25/0.55          | ~ (m1_pre_topc @ X35 @ X34)
% 0.25/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.25/0.55          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.25/0.55               X36)
% 0.25/0.55          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X39)
% 0.25/0.55          | ((X39) != (X36))
% 0.25/0.55          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X34))
% 0.25/0.55          | ~ (m1_subset_1 @ X38 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.25/0.55          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.25/0.55          | ~ (v1_funct_1 @ X38)
% 0.25/0.55          | ~ (l1_pre_topc @ X37)
% 0.25/0.55          | ~ (v2_pre_topc @ X37)
% 0.25/0.55          | (v2_struct_0 @ X37))),
% 0.25/0.55      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.25/0.55  thf('71', plain,
% 0.25/0.55      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X37)
% 0.25/0.55          | ~ (v2_pre_topc @ X37)
% 0.25/0.55          | ~ (l1_pre_topc @ X37)
% 0.25/0.55          | ~ (v1_funct_1 @ X38)
% 0.25/0.55          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))
% 0.25/0.55          | ~ (m1_subset_1 @ X38 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X37))))
% 0.25/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.25/0.55          | (r1_tmap_1 @ X34 @ X37 @ X38 @ X36)
% 0.25/0.55          | ~ (r1_tmap_1 @ X35 @ X37 @ (k2_tmap_1 @ X34 @ X37 @ X38 @ X35) @ 
% 0.25/0.55               X36)
% 0.25/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 0.25/0.55          | ~ (m1_pre_topc @ X35 @ X34)
% 0.25/0.55          | ~ (v1_tsep_1 @ X35 @ X34)
% 0.25/0.55          | (v2_struct_0 @ X35)
% 0.25/0.55          | ~ (l1_pre_topc @ X34)
% 0.25/0.55          | ~ (v2_pre_topc @ X34)
% 0.25/0.55          | (v2_struct_0 @ X34))),
% 0.25/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.25/0.55  thf('72', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_D)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.25/0.55          | (v2_struct_0 @ X0)
% 0.25/0.55          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.25/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.25/0.55               X1)
% 0.25/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.25/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.25/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['69', '71'])).
% 0.25/0.55  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.25/0.55  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.55  thf('75', plain,
% 0.25/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('79', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_D)
% 0.25/0.55          | (v2_struct_0 @ X0)
% 0.25/0.55          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.25/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.25/0.55               X1)
% 0.25/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.25/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.25/0.55          | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)],
% 0.25/0.55                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.25/0.55  thf('80', plain,
% 0.25/0.55      ((((v2_struct_0 @ sk_A)
% 0.25/0.55         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.25/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.25/0.55         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.25/0.55         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.25/0.55         | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.25/0.55         | (v2_struct_0 @ sk_C)
% 0.25/0.55         | (v2_struct_0 @ sk_D)))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['68', '79'])).
% 0.25/0.55  thf('81', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('82', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.25/0.55  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('84', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t1_tsep_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.55           ( m1_subset_1 @
% 0.25/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.25/0.55  thf('85', plain,
% 0.25/0.55      (![X26 : $i, X27 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X26 @ X27)
% 0.25/0.55          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.25/0.55          | ~ (l1_pre_topc @ X27))),
% 0.25/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.25/0.55  thf('86', plain,
% 0.25/0.55      ((~ (l1_pre_topc @ sk_D)
% 0.25/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.25/0.55  thf('87', plain, ((l1_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.55  thf('88', plain,
% 0.25/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.25/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.25/0.55  thf(t16_tsep_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.25/0.55                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.25/0.55                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('89', plain,
% 0.25/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X23 @ X24)
% 0.25/0.55          | ((X25) != (u1_struct_0 @ X23))
% 0.25/0.55          | ~ (v3_pre_topc @ X25 @ X24)
% 0.25/0.55          | (v1_tsep_1 @ X23 @ X24)
% 0.25/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.55          | ~ (l1_pre_topc @ X24)
% 0.25/0.55          | ~ (v2_pre_topc @ X24))),
% 0.25/0.55      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.25/0.55  thf('90', plain,
% 0.25/0.55      (![X23 : $i, X24 : $i]:
% 0.25/0.55         (~ (v2_pre_topc @ X24)
% 0.25/0.55          | ~ (l1_pre_topc @ X24)
% 0.25/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.25/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.55          | (v1_tsep_1 @ X23 @ X24)
% 0.25/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.25/0.55          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.25/0.55      inference('simplify', [status(thm)], ['89'])).
% 0.25/0.55  thf('91', plain,
% 0.25/0.55      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.25/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.25/0.55        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_D)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_D))),
% 0.25/0.55      inference('sup-', [status(thm)], ['88', '90'])).
% 0.25/0.55  thf('92', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.55  thf('94', plain, ((v2_pre_topc @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.25/0.55  thf('95', plain,
% 0.25/0.55      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.25/0.55        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.25/0.55      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.25/0.55  thf('96', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('97', plain,
% 0.25/0.55      (![X26 : $i, X27 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X26 @ X27)
% 0.25/0.55          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.25/0.55          | ~ (l1_pre_topc @ X27))),
% 0.25/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.25/0.55  thf('98', plain,
% 0.25/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.25/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.25/0.55  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('100', plain,
% 0.25/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.25/0.55  thf('101', plain,
% 0.25/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.25/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.25/0.55  thf(t33_tops_2, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.25/0.55               ( ( v3_pre_topc @ B @ A ) =>
% 0.25/0.55                 ( ![D:$i]:
% 0.25/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.25/0.55                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('102', plain,
% 0.25/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.25/0.55          | ~ (v3_pre_topc @ X10 @ X11)
% 0.25/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | (v3_pre_topc @ X12 @ X13)
% 0.25/0.55          | ((X12) != (X10))
% 0.25/0.55          | ~ (m1_pre_topc @ X13 @ X11)
% 0.25/0.55          | ~ (l1_pre_topc @ X11))),
% 0.25/0.55      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.25/0.55  thf('103', plain,
% 0.25/0.55      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ X11)
% 0.25/0.55          | ~ (m1_pre_topc @ X13 @ X11)
% 0.25/0.55          | (v3_pre_topc @ X10 @ X13)
% 0.25/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (v3_pre_topc @ X10 @ X11)
% 0.25/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.25/0.55      inference('simplify', [status(thm)], ['102'])).
% 0.25/0.55  thf('104', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.25/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.25/0.55          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.25/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.55          | ~ (l1_pre_topc @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['101', '103'])).
% 0.25/0.55  thf('105', plain,
% 0.25/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.25/0.55        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.25/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.25/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['100', '104'])).
% 0.25/0.55  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('107', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('108', plain,
% 0.25/0.55      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.25/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B))),
% 0.25/0.55      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.25/0.55  thf('109', plain,
% 0.25/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.25/0.55  thf('110', plain,
% 0.25/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X23 @ X24)
% 0.25/0.55          | ((X25) != (u1_struct_0 @ X23))
% 0.25/0.55          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.25/0.55          | ~ (m1_pre_topc @ X23 @ X24)
% 0.25/0.55          | (v3_pre_topc @ X25 @ X24)
% 0.25/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.55          | ~ (l1_pre_topc @ X24)
% 0.25/0.55          | ~ (v2_pre_topc @ X24))),
% 0.25/0.55      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.25/0.55  thf('111', plain,
% 0.25/0.55      (![X23 : $i, X24 : $i]:
% 0.25/0.55         (~ (v2_pre_topc @ X24)
% 0.25/0.55          | ~ (l1_pre_topc @ X24)
% 0.25/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.25/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.55          | (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.25/0.55          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.25/0.55          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.25/0.55      inference('simplify', [status(thm)], ['110'])).
% 0.25/0.55  thf('112', plain,
% 0.25/0.55      ((~ (m1_pre_topc @ sk_C @ sk_B)
% 0.25/0.55        | ~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.25/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['109', '111'])).
% 0.25/0.55  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('114', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('115', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('116', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('117', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)),
% 0.25/0.55      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.25/0.55  thf('118', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['108', '117'])).
% 0.25/0.55  thf('119', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['95', '118'])).
% 0.25/0.55  thf('120', plain,
% 0.25/0.55      ((((v2_struct_0 @ sk_A)
% 0.25/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.25/0.55         | (v2_struct_0 @ sk_C)
% 0.25/0.55         | (v2_struct_0 @ sk_D)))
% 0.25/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('demod', [status(thm)], ['80', '81', '82', '83', '119'])).
% 0.25/0.55  thf('121', plain,
% 0.25/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.25/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.25/0.55      inference('split', [status(esa)], ['10'])).
% 0.25/0.55  thf('122', plain,
% 0.25/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.25/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.25/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['120', '121'])).
% 0.25/0.55  thf('123', plain, (~ (v2_struct_0 @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('124', plain,
% 0.25/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.25/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.25/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('clc', [status(thm)], ['122', '123'])).
% 0.25/0.55  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('126', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_C))
% 0.25/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.25/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.25/0.55      inference('clc', [status(thm)], ['124', '125'])).
% 0.25/0.55  thf('127', plain, (~ (v2_struct_0 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('128', plain,
% 0.25/0.55      (~
% 0.25/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.25/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('sup-', [status(thm)], ['126', '127'])).
% 0.25/0.55  thf('129', plain,
% 0.25/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.25/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.25/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.25/0.55      inference('split', [status(esa)], ['8'])).
% 0.25/0.55  thf('130', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.25/0.55      inference('sat_resolution*', [status(thm)], ['14', '18', '128', '129'])).
% 0.25/0.55  thf('131', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.25/0.55      inference('simpl_trail', [status(thm)], ['5', '130'])).
% 0.25/0.55  thf('132', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_E @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t64_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.55                 ( m1_subset_1 @
% 0.25/0.55                   C @ 
% 0.25/0.55                   ( k1_zfmisc_1 @
% 0.25/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.55                   ( ![E:$i]:
% 0.25/0.55                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.25/0.55                       ( ![F:$i]:
% 0.25/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.55                           ( ( ( ( E ) = ( F ) ) & 
% 0.25/0.55                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.25/0.55                             ( r1_tmap_1 @
% 0.25/0.55                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('133', plain,
% 0.25/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X28)
% 0.25/0.55          | ~ (v2_pre_topc @ X28)
% 0.25/0.55          | ~ (l1_pre_topc @ X28)
% 0.25/0.55          | (v2_struct_0 @ X29)
% 0.25/0.55          | ~ (m1_pre_topc @ X29 @ X28)
% 0.25/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.25/0.55          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.25/0.55          | ((X33) != (X30))
% 0.25/0.55          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X33)
% 0.25/0.55          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.25/0.55          | ~ (m1_subset_1 @ X32 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.25/0.55          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.25/0.55          | ~ (v1_funct_1 @ X32)
% 0.25/0.55          | ~ (l1_pre_topc @ X31)
% 0.25/0.55          | ~ (v2_pre_topc @ X31)
% 0.25/0.55          | (v2_struct_0 @ X31))),
% 0.25/0.55      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.25/0.55  thf('134', plain,
% 0.40/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.55         ((v2_struct_0 @ X31)
% 0.40/0.55          | ~ (v2_pre_topc @ X31)
% 0.40/0.55          | ~ (l1_pre_topc @ X31)
% 0.40/0.55          | ~ (v1_funct_1 @ X32)
% 0.40/0.55          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.40/0.55          | ~ (m1_subset_1 @ X32 @ 
% 0.40/0.55               (k1_zfmisc_1 @ 
% 0.40/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.40/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.40/0.55          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X30)
% 0.40/0.55          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.40/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.40/0.55          | ~ (m1_pre_topc @ X29 @ X28)
% 0.40/0.55          | (v2_struct_0 @ X29)
% 0.40/0.55          | ~ (l1_pre_topc @ X28)
% 0.40/0.55          | ~ (v2_pre_topc @ X28)
% 0.40/0.55          | (v2_struct_0 @ X28))),
% 0.40/0.55      inference('simplify', [status(thm)], ['133'])).
% 0.40/0.55  thf('135', plain,
% 0.40/0.55      (![X0 : $i, X1 : $i]:
% 0.40/0.55         ((v2_struct_0 @ sk_D)
% 0.40/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.40/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.40/0.55          | (v2_struct_0 @ X0)
% 0.40/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.40/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.40/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.40/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.40/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.40/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.40/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.40/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.55          | (v2_struct_0 @ sk_A))),
% 0.40/0.55      inference('sup-', [status(thm)], ['132', '134'])).
% 0.40/0.55  thf('136', plain, ((v2_pre_topc @ sk_D)),
% 0.40/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.40/0.55  thf('137', plain, ((l1_pre_topc @ sk_D)),
% 0.40/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.55  thf('138', plain,
% 0.40/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('139', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('142', plain,
% 0.40/0.55      (![X0 : $i, X1 : $i]:
% 0.40/0.55         ((v2_struct_0 @ sk_D)
% 0.40/0.55          | (v2_struct_0 @ X0)
% 0.40/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.40/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.40/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.40/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.40/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.40/0.55          | (v2_struct_0 @ sk_A))),
% 0.40/0.55      inference('demod', [status(thm)],
% 0.40/0.55                ['135', '136', '137', '138', '139', '140', '141'])).
% 0.40/0.55  thf('143', plain,
% 0.40/0.55      (![X0 : $i]:
% 0.40/0.55         ((v2_struct_0 @ sk_A)
% 0.40/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.40/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.40/0.55             sk_F)
% 0.40/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.40/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.40/0.55          | (v2_struct_0 @ X0)
% 0.40/0.55          | (v2_struct_0 @ sk_D))),
% 0.40/0.55      inference('sup-', [status(thm)], ['131', '142'])).
% 0.40/0.55  thf('144', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('145', plain,
% 0.40/0.55      (![X0 : $i]:
% 0.40/0.55         ((v2_struct_0 @ sk_A)
% 0.40/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.40/0.55             sk_F)
% 0.40/0.55          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.40/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.40/0.55          | (v2_struct_0 @ X0)
% 0.40/0.55          | (v2_struct_0 @ sk_D))),
% 0.40/0.55      inference('demod', [status(thm)], ['143', '144'])).
% 0.40/0.55  thf('146', plain,
% 0.40/0.55      (((v2_struct_0 @ sk_D)
% 0.40/0.55        | (v2_struct_0 @ sk_C)
% 0.40/0.55        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.40/0.55        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.40/0.55           sk_F)
% 0.40/0.55        | (v2_struct_0 @ sk_A))),
% 0.40/0.55      inference('sup-', [status(thm)], ['3', '145'])).
% 0.40/0.55  thf('147', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('148', plain,
% 0.40/0.55      (((v2_struct_0 @ sk_D)
% 0.40/0.55        | (v2_struct_0 @ sk_C)
% 0.40/0.55        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.40/0.55           sk_F)
% 0.40/0.55        | (v2_struct_0 @ sk_A))),
% 0.40/0.55      inference('demod', [status(thm)], ['146', '147'])).
% 0.40/0.55  thf('149', plain,
% 0.40/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.40/0.55         <= (~
% 0.40/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.40/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.55  thf('150', plain,
% 0.40/0.55      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.40/0.55         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.40/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.40/0.55  thf('151', plain,
% 0.40/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.40/0.55           sk_F))
% 0.40/0.55         <= (~
% 0.40/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.40/0.55      inference('demod', [status(thm)], ['149', '150'])).
% 0.40/0.55  thf('152', plain,
% 0.40/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.40/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.40/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.55  thf('153', plain,
% 0.40/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.40/0.55         <= (~
% 0.40/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.40/0.55      inference('split', [status(esa)], ['17'])).
% 0.40/0.55  thf('154', plain,
% 0.40/0.55      (~
% 0.40/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.40/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.40/0.55      inference('sup-', [status(thm)], ['152', '153'])).
% 0.40/0.55  thf('155', plain,
% 0.40/0.55      (~
% 0.40/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.40/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.40/0.55      inference('sat_resolution*', [status(thm)], ['14', '18', '128', '154'])).
% 0.40/0.55  thf('156', plain,
% 0.40/0.55      (~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.40/0.55          sk_F)),
% 0.40/0.55      inference('simpl_trail', [status(thm)], ['151', '155'])).
% 0.40/0.55  thf('157', plain,
% 0.40/0.55      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.40/0.55      inference('sup-', [status(thm)], ['148', '156'])).
% 0.40/0.55  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('159', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.40/0.55      inference('clc', [status(thm)], ['157', '158'])).
% 0.40/0.55  thf('160', plain, (~ (v2_struct_0 @ sk_D)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('161', plain, ((v2_struct_0 @ sk_C)),
% 0.40/0.55      inference('clc', [status(thm)], ['159', '160'])).
% 0.40/0.55  thf('162', plain, ($false), inference('demod', [status(thm)], ['0', '161'])).
% 0.40/0.55  
% 0.40/0.55  % SZS output end Refutation
% 0.40/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
