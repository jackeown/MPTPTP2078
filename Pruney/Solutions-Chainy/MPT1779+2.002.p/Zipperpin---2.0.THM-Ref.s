%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nfwPmEEZ2h

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:40 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  369 (5143 expanded)
%              Number of leaves         :   31 (1493 expanded)
%              Depth                    :   31
%              Number of atoms          : 5257 (350533 expanded)
%              Number of equality atoms :   73 ( 678 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t90_tmap_1,conjecture,(
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
                     => ( ( ( m1_pre_topc @ C @ D )
                          & ( m1_pre_topc @ E @ C ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) )
                                & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B )
                                & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B )
                                & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( m1_pre_topc @ C @ D )
                            & ( m1_pre_topc @ E @ C ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) )
                                  & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                  & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B )
                                  & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) )
                                  & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                                  & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B )
                                  & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t90_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) @ ( k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ ( k2_tmap_1 @ X24 @ X22 @ X26 @ X23 ) ) @ ( k2_tmap_1 @ X24 @ X22 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('23',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_E @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('34',plain,(
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

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('58',plain,(
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

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('62',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('91',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','94','99','100','101','102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('111',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('112',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','118','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

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

thf('126',plain,(
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

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('130',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['127','130','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

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

thf('146',plain,(
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

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
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

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['149','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['148','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('168',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('172',plain,(
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

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('175',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('176',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174','175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['170','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['147','168','187'])).

thf('189',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','77','78'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['189','195'])).

thf('197',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('198',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ X0 )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','203','204'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference('sup-',[status(thm)],['120','205'])).

thf('207',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
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

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['211','212','213','214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['208','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['207','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['228','235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['225','241'])).

thf('243',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
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

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['247','248','249','250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['244','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['243','256'])).

thf('258',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('259',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
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

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['268','269','270','271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['265','273'])).

thf('275',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['274','275','276'])).

thf('278',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['264','277'])).

thf('279',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('280',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['280','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['206','242','263','284'])).

thf('286',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('287',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf(t89_tmap_1,axiom,(
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
                        & ( v5_pre_topc @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf('289',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X33 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X32 @ X30 @ X33 @ X31 @ X34 ) @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v5_pre_topc @ X34 @ X33 @ X30 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t89_tmap_1])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_C @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('292',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('293',plain,(
    v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('295',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['290','291','292','295','296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['287','298'])).

thf('300',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('301',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ sk_E @ sk_B )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['286','302'])).

thf('304',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('305',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['285','306'])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['309'])).

thf('311',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('312',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('314',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('315',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['309'])).

thf('316',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['313','316'])).

thf('318',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('319',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['309'])).

thf('320',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('322',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('323',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['309'])).

thf('324',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['321','324'])).

thf('326',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['309'])).

thf('327',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['317','320','325','326'])).

thf('328',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['312','327'])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['308','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['333','334'])).

thf('336',plain,(
    $false ),
    inference(demod,[status(thm)],['0','335'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nfwPmEEZ2h
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 520 iterations in 0.329s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.80  thf(sk_F_type, type, sk_F: $i).
% 0.59/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.80  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.59/0.80  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.59/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.80  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.59/0.80  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.59/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.59/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.80  thf(t90_tmap_1, conjecture,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.80             ( l1_pre_topc @ B ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.80               ( ![D:$i]:
% 0.59/0.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.80                   ( ![E:$i]:
% 0.59/0.80                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.59/0.80                       ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 0.59/0.80                         ( ![F:$i]:
% 0.59/0.80                           ( ( ( v1_funct_1 @ F ) & 
% 0.59/0.80                               ( v1_funct_2 @
% 0.59/0.80                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                               ( m1_subset_1 @
% 0.59/0.80                                 F @ 
% 0.59/0.80                                 ( k1_zfmisc_1 @
% 0.59/0.80                                   ( k2_zfmisc_1 @
% 0.59/0.80                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                             ( ( ( v1_funct_1 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 0.59/0.80                                 ( v1_funct_2 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 0.59/0.80                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                                 ( v5_pre_topc @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 0.59/0.80                                 ( m1_subset_1 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 0.59/0.80                                   ( k1_zfmisc_1 @
% 0.59/0.80                                     ( k2_zfmisc_1 @
% 0.59/0.80                                       ( u1_struct_0 @ C ) @ 
% 0.59/0.80                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                               ( ( v1_funct_1 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 0.59/0.80                                 ( v1_funct_2 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 0.59/0.80                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                                 ( v5_pre_topc @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 0.59/0.80                                 ( m1_subset_1 @
% 0.59/0.80                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 0.59/0.80                                   ( k1_zfmisc_1 @
% 0.59/0.80                                     ( k2_zfmisc_1 @
% 0.59/0.80                                       ( u1_struct_0 @ E ) @ 
% 0.59/0.80                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i]:
% 0.59/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.80            ( l1_pre_topc @ A ) ) =>
% 0.59/0.80          ( ![B:$i]:
% 0.59/0.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.80                ( l1_pre_topc @ B ) ) =>
% 0.59/0.80              ( ![C:$i]:
% 0.59/0.80                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.80                  ( ![D:$i]:
% 0.59/0.80                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.80                      ( ![E:$i]:
% 0.59/0.80                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.59/0.80                          ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 0.59/0.80                            ( ![F:$i]:
% 0.59/0.80                              ( ( ( v1_funct_1 @ F ) & 
% 0.59/0.80                                  ( v1_funct_2 @
% 0.59/0.80                                    F @ ( u1_struct_0 @ D ) @ 
% 0.59/0.80                                    ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                                  ( m1_subset_1 @
% 0.59/0.80                                    F @ 
% 0.59/0.80                                    ( k1_zfmisc_1 @
% 0.59/0.80                                      ( k2_zfmisc_1 @
% 0.59/0.80                                        ( u1_struct_0 @ D ) @ 
% 0.59/0.80                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                                ( ( ( v1_funct_1 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 0.59/0.80                                    ( v1_funct_2 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 0.59/0.80                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                                    ( v5_pre_topc @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 0.59/0.80                                    ( m1_subset_1 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 0.59/0.80                                      ( k1_zfmisc_1 @
% 0.59/0.80                                        ( k2_zfmisc_1 @
% 0.59/0.80                                          ( u1_struct_0 @ C ) @ 
% 0.59/0.80                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                                  ( ( v1_funct_1 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 0.59/0.80                                    ( v1_funct_2 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 0.59/0.80                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                                    ( v5_pre_topc @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 0.59/0.80                                    ( m1_subset_1 @
% 0.59/0.80                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 0.59/0.80                                      ( k1_zfmisc_1 @
% 0.59/0.80                                        ( k2_zfmisc_1 @
% 0.59/0.80                                          ( u1_struct_0 @ E ) @ 
% 0.59/0.80                                          ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t90_tmap_1])).
% 0.59/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('2', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t7_tsep_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_pre_topc @ B @ A ) =>
% 0.59/0.80           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X27 @ X28)
% 0.59/0.80          | (m1_pre_topc @ X29 @ X28)
% 0.59/0.80          | ~ (m1_pre_topc @ X29 @ X27)
% 0.59/0.80          | ~ (l1_pre_topc @ X28)
% 0.59/0.80          | ~ (v2_pre_topc @ X28))),
% 0.59/0.80      inference('cnf', [status(esa)], [t7_tsep_1])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ sk_D)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.80          | (m1_pre_topc @ X0 @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.80  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(cc1_pre_topc, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X4 @ X5)
% 0.59/0.80          | (v2_pre_topc @ X4)
% 0.59/0.80          | ~ (l1_pre_topc @ X5)
% 0.59/0.80          | ~ (v2_pre_topc @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.80  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('11', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.80  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_m1_pre_topc, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.80  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.80  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_C) | (m1_pre_topc @ X0 @ sk_D))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.59/0.80  thf('18', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '17'])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_F @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t78_tmap_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.80             ( l1_pre_topc @ B ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.80               ( ![D:$i]:
% 0.59/0.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.80                   ( ![E:$i]:
% 0.59/0.80                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.80                         ( v1_funct_2 @
% 0.59/0.80                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                         ( m1_subset_1 @
% 0.59/0.80                           E @ 
% 0.59/0.80                           ( k1_zfmisc_1 @
% 0.59/0.80                             ( k2_zfmisc_1 @
% 0.59/0.80                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                       ( ( m1_pre_topc @ C @ D ) =>
% 0.59/0.80                         ( r2_funct_2 @
% 0.59/0.80                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.59/0.80                           ( k3_tmap_1 @
% 0.59/0.80                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.59/0.80                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X22)
% 0.59/0.80          | ~ (v2_pre_topc @ X22)
% 0.59/0.80          | ~ (l1_pre_topc @ X22)
% 0.59/0.80          | (v2_struct_0 @ X23)
% 0.59/0.80          | ~ (m1_pre_topc @ X23 @ X24)
% 0.59/0.80          | ~ (m1_pre_topc @ X25 @ X23)
% 0.59/0.80          | (r2_funct_2 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 0.59/0.80             (k3_tmap_1 @ X24 @ X22 @ X23 @ X25 @ 
% 0.59/0.80              (k2_tmap_1 @ X24 @ X22 @ X26 @ X23)) @ 
% 0.59/0.80             (k2_tmap_1 @ X24 @ X22 @ X26 @ X25))
% 0.59/0.80          | ~ (m1_subset_1 @ X26 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 0.59/0.80          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 0.59/0.80          | ~ (v1_funct_1 @ X26)
% 0.59/0.80          | ~ (m1_pre_topc @ X25 @ X24)
% 0.59/0.80          | (v2_struct_0 @ X25)
% 0.59/0.80          | ~ (l1_pre_topc @ X24)
% 0.59/0.80          | ~ (v2_pre_topc @ X24)
% 0.59/0.80          | (v2_struct_0 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_D)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.80          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X1)) @ 
% 0.59/0.80             (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.80  thf('22', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.80  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X1)) @ 
% 0.59/0.80             (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)],
% 0.59/0.80                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_E @ X0)
% 0.59/0.80          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)) @ 
% 0.59/0.80             (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 0.59/0.80          | (v2_struct_0 @ sk_E)
% 0.59/0.80          | (v2_struct_0 @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['18', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_D)
% 0.59/0.80        | (v2_struct_0 @ sk_E)
% 0.59/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80           (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80           (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 0.59/0.80        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.59/0.80        | (v2_struct_0 @ sk_C)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '29'])).
% 0.59/0.80  thf('31', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '17'])).
% 0.59/0.80  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(d5_tmap_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.80             ( l1_pre_topc @ B ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( m1_pre_topc @ C @ A ) =>
% 0.59/0.80               ( ![D:$i]:
% 0.59/0.80                 ( ( m1_pre_topc @ D @ A ) =>
% 0.59/0.80                   ( ![E:$i]:
% 0.59/0.80                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.80                         ( v1_funct_2 @
% 0.59/0.80                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                         ( m1_subset_1 @
% 0.59/0.80                           E @ 
% 0.59/0.80                           ( k1_zfmisc_1 @
% 0.59/0.80                             ( k2_zfmisc_1 @
% 0.59/0.80                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80                       ( ( m1_pre_topc @ D @ C ) =>
% 0.59/0.80                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.59/0.80                           ( k2_partfun1 @
% 0.59/0.80                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.59/0.80                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X12)
% 0.59/0.80          | ~ (v2_pre_topc @ X12)
% 0.59/0.80          | ~ (l1_pre_topc @ X12)
% 0.59/0.80          | ~ (m1_pre_topc @ X13 @ X14)
% 0.59/0.80          | ~ (m1_pre_topc @ X13 @ X15)
% 0.59/0.80          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.59/0.80                 X16 @ (u1_struct_0 @ X13)))
% 0.59/0.80          | ~ (m1_subset_1 @ X16 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.59/0.80          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.59/0.80          | ~ (v1_funct_1 @ X16)
% 0.59/0.80          | ~ (m1_pre_topc @ X15 @ X14)
% 0.59/0.80          | ~ (l1_pre_topc @ X14)
% 0.59/0.80          | ~ (v2_pre_topc @ X14)
% 0.59/0.80          | (v2_struct_0 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.80          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 0.59/0.80          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80                 (u1_struct_0 @ X1)))
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.80          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80                 (u1_struct_0 @ X1)))
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.59/0.80  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_F @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X12)
% 0.59/0.80          | ~ (v2_pre_topc @ X12)
% 0.59/0.80          | ~ (l1_pre_topc @ X12)
% 0.59/0.80          | ~ (m1_pre_topc @ X13 @ X14)
% 0.59/0.80          | ~ (m1_pre_topc @ X13 @ X15)
% 0.59/0.80          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.59/0.80                 X16 @ (u1_struct_0 @ X13)))
% 0.59/0.80          | ~ (m1_subset_1 @ X16 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.59/0.80          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.59/0.80          | ~ (v1_funct_1 @ X16)
% 0.59/0.80          | ~ (m1_pre_topc @ X15 @ X14)
% 0.59/0.80          | ~ (l1_pre_topc @ X14)
% 0.59/0.80          | ~ (v2_pre_topc @ X14)
% 0.59/0.80          | (v2_struct_0 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.80          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.80          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X1)))
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf('46', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.80          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X1)))
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['42', '50'])).
% 0.59/0.80  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('54', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.80          | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               sk_F @ (u1_struct_0 @ sk_C)))
% 0.59/0.80        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['41', '54'])).
% 0.59/0.80  thf('56', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_F @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(d4_tmap_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.80             ( l1_pre_topc @ B ) ) =>
% 0.59/0.80           ( ![C:$i]:
% 0.59/0.80             ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80                 ( m1_subset_1 @
% 0.59/0.80                   C @ 
% 0.59/0.80                   ( k1_zfmisc_1 @
% 0.59/0.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80               ( ![D:$i]:
% 0.59/0.80                 ( ( m1_pre_topc @ D @ A ) =>
% 0.59/0.80                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.59/0.80                     ( k2_partfun1 @
% 0.59/0.80                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.59/0.80                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X8)
% 0.59/0.80          | ~ (v2_pre_topc @ X8)
% 0.59/0.80          | ~ (l1_pre_topc @ X8)
% 0.59/0.80          | ~ (m1_pre_topc @ X9 @ X10)
% 0.59/0.80          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.59/0.80                 X11 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.59/0.80          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.59/0.80          | ~ (v1_funct_1 @ X11)
% 0.59/0.80          | ~ (l1_pre_topc @ X10)
% 0.59/0.80          | ~ (v2_pre_topc @ X10)
% 0.59/0.80          | (v2_struct_0 @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_D)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.80          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.80          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.80  thf('60', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.80  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('62', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_D)
% 0.59/0.80          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)],
% 0.59/0.80                ['59', '60', '61', '62', '63', '64', '65'])).
% 0.59/0.80  thf('67', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               sk_F @ (u1_struct_0 @ sk_C)))
% 0.59/0.80        | (v2_struct_0 @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['56', '66'])).
% 0.59/0.80  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('69', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_D)
% 0.59/0.80        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               sk_F @ (u1_struct_0 @ sk_C))))),
% 0.59/0.80      inference('clc', [status(thm)], ['67', '68'])).
% 0.59/0.80  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 0.59/0.80         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.59/0.80            (u1_struct_0 @ sk_C)))),
% 0.59/0.80      inference('clc', [status(thm)], ['69', '70'])).
% 0.59/0.80  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('73', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['55', '71', '72'])).
% 0.59/0.80  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('75', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 0.59/0.80      inference('clc', [status(thm)], ['73', '74'])).
% 0.59/0.80  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('78', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('79', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.80          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X1)))
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.80          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['40', '77', '78'])).
% 0.59/0.80  thf('80', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.80          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.80          | (v2_struct_0 @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['32', '79'])).
% 0.59/0.80  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('82', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.80      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.80  thf('83', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.80          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 0.59/0.80          | (v2_struct_0 @ sk_D))),
% 0.59/0.80      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.59/0.80  thf('84', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_D)
% 0.59/0.80        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))
% 0.59/0.80        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['31', '83'])).
% 0.59/0.80  thf('85', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('86', plain,
% 0.59/0.80      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('87', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X8)
% 0.59/0.80          | ~ (v2_pre_topc @ X8)
% 0.59/0.80          | ~ (l1_pre_topc @ X8)
% 0.59/0.80          | ~ (m1_pre_topc @ X9 @ X10)
% 0.59/0.80          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.59/0.80                 X11 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.59/0.80          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.59/0.80          | ~ (v1_funct_1 @ X11)
% 0.59/0.80          | ~ (l1_pre_topc @ X10)
% 0.59/0.80          | ~ (v2_pre_topc @ X10)
% 0.59/0.80          | (v2_struct_0 @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.59/0.80  thf('88', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_C)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_C)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_C)
% 0.59/0.80          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 0.59/0.80          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80                 (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.80  thf('89', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('90', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X4 @ X5)
% 0.59/0.80          | (v2_pre_topc @ X4)
% 0.59/0.80          | ~ (l1_pre_topc @ X5)
% 0.59/0.80          | ~ (v2_pre_topc @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.59/0.80  thf('91', plain,
% 0.59/0.80      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['89', '90'])).
% 0.59/0.80  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('94', plain, ((v2_pre_topc @ sk_C)),
% 0.59/0.80      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.59/0.80  thf('95', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('96', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.80  thf('97', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['95', '96'])).
% 0.59/0.80  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('99', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.80      inference('demod', [status(thm)], ['97', '98'])).
% 0.59/0.80  thf('100', plain,
% 0.59/0.80      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('101', plain,
% 0.59/0.80      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('104', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ sk_C)
% 0.59/0.80          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0)
% 0.59/0.80              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80                 (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.80          | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)],
% 0.59/0.80                ['88', '94', '99', '100', '101', '102', '103'])).
% 0.59/0.80  thf('105', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80               (u1_struct_0 @ sk_E)))
% 0.59/0.80        | (v2_struct_0 @ sk_C))),
% 0.59/0.80      inference('sup-', [status(thm)], ['85', '104'])).
% 0.59/0.80  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('107', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_C)
% 0.59/0.80        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 0.59/0.80            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80               (u1_struct_0 @ sk_E))))),
% 0.59/0.80      inference('clc', [status(thm)], ['105', '106'])).
% 0.59/0.80  thf('108', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('109', plain,
% 0.59/0.80      (((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 0.59/0.80         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80            (u1_struct_0 @ sk_E)))),
% 0.59/0.80      inference('clc', [status(thm)], ['107', '108'])).
% 0.59/0.80  thf('110', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('111', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('112', plain,
% 0.59/0.80      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80         sk_E)
% 0.59/0.80         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 0.59/0.80      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.59/0.80  thf('113', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('114', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_D)
% 0.59/0.80        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['84', '112', '113'])).
% 0.59/0.80  thf('115', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('116', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)))),
% 0.59/0.80      inference('clc', [status(thm)], ['114', '115'])).
% 0.59/0.80  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('118', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80         = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))),
% 0.59/0.80      inference('clc', [status(thm)], ['116', '117'])).
% 0.59/0.80  thf('119', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('120', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_D)
% 0.59/0.80        | (v2_struct_0 @ sk_E)
% 0.59/0.80        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80           (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 0.59/0.80           (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 0.59/0.80        | (v2_struct_0 @ sk_C)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['30', '118', '119'])).
% 0.59/0.80  thf('121', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('122', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('123', plain,
% 0.59/0.80      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('124', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('125', plain,
% 0.59/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('demod', [status(thm)], ['123', '124'])).
% 0.59/0.80  thf(dt_k3_tmap_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.80         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.59/0.80         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.59/0.80         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.59/0.80         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.80         ( m1_subset_1 @
% 0.59/0.80           E @ 
% 0.59/0.80           ( k1_zfmisc_1 @
% 0.59/0.80             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.80       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.59/0.80         ( v1_funct_2 @
% 0.59/0.80           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.59/0.80           ( u1_struct_0 @ B ) ) & 
% 0.59/0.80         ( m1_subset_1 @
% 0.59/0.80           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.59/0.80           ( k1_zfmisc_1 @
% 0.59/0.80             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.80  thf('126', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.80          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.80          | ~ (l1_pre_topc @ X20)
% 0.59/0.80          | ~ (v2_pre_topc @ X20)
% 0.59/0.80          | (v2_struct_0 @ X20)
% 0.59/0.80          | ~ (l1_pre_topc @ X18)
% 0.59/0.80          | ~ (v2_pre_topc @ X18)
% 0.59/0.80          | (v2_struct_0 @ X18)
% 0.59/0.80          | ~ (v1_funct_1 @ X21)
% 0.59/0.80          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.80          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.80          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.59/0.80             (k1_zfmisc_1 @ 
% 0.59/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.80  thf('127', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((m1_subset_1 @ 
% 0.59/0.80           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80           (k1_zfmisc_1 @ 
% 0.59/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | ~ (v2_pre_topc @ X1)
% 0.59/0.80          | ~ (l1_pre_topc @ X1)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['125', '126'])).
% 0.59/0.80  thf('128', plain,
% 0.59/0.80      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('129', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('130', plain,
% 0.59/0.80      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['128', '129'])).
% 0.59/0.80  thf('131', plain,
% 0.59/0.80      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('132', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('133', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('demod', [status(thm)], ['131', '132'])).
% 0.59/0.80  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('136', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((m1_subset_1 @ 
% 0.59/0.80           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80           (k1_zfmisc_1 @ 
% 0.59/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | ~ (v2_pre_topc @ X1)
% 0.59/0.80          | ~ (l1_pre_topc @ X1)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['127', '130', '133', '134', '135'])).
% 0.59/0.80  thf('137', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (m1_subset_1 @ 
% 0.59/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80             (k1_zfmisc_1 @ 
% 0.59/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['122', '136'])).
% 0.59/0.80  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('140', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (m1_subset_1 @ 
% 0.59/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80             (k1_zfmisc_1 @ 
% 0.59/0.80              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.80      inference('demod', [status(thm)], ['137', '138', '139'])).
% 0.59/0.80  thf('141', plain,
% 0.59/0.80      (((m1_subset_1 @ 
% 0.59/0.80         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80          (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80         (k1_zfmisc_1 @ 
% 0.59/0.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['121', '140'])).
% 0.59/0.80  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('143', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | (m1_subset_1 @ 
% 0.59/0.80           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80           (k1_zfmisc_1 @ 
% 0.59/0.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.80      inference('clc', [status(thm)], ['141', '142'])).
% 0.59/0.80  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('145', plain,
% 0.59/0.80      ((m1_subset_1 @ 
% 0.59/0.80        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('clc', [status(thm)], ['143', '144'])).
% 0.59/0.80  thf(redefinition_r2_funct_2, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.80         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.80       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.59/0.80  thf('146', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.59/0.80          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.59/0.80          | ~ (v1_funct_1 @ X0)
% 0.59/0.80          | ~ (v1_funct_1 @ X3)
% 0.59/0.80          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.59/0.80          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.59/0.80          | ((X0) = (X3))
% 0.59/0.80          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.59/0.80  thf('147', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80             X0)
% 0.59/0.80          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) = (X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.80          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ~ (v1_funct_1 @ X0)
% 0.59/0.80          | ~ (v1_funct_1 @ 
% 0.59/0.80               (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80                (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))
% 0.59/0.80          | ~ (v1_funct_2 @ 
% 0.59/0.80               (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80                (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['145', '146'])).
% 0.59/0.80  thf('148', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('149', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('150', plain,
% 0.59/0.80      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('151', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.80          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.80          | ~ (l1_pre_topc @ X20)
% 0.59/0.80          | ~ (v2_pre_topc @ X20)
% 0.59/0.80          | (v2_struct_0 @ X20)
% 0.59/0.80          | ~ (l1_pre_topc @ X18)
% 0.59/0.80          | ~ (v2_pre_topc @ X18)
% 0.59/0.80          | (v2_struct_0 @ X18)
% 0.59/0.80          | ~ (v1_funct_1 @ X21)
% 0.59/0.80          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.80          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.80          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.80  thf('152', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_funct_1 @ 
% 0.59/0.80           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 0.59/0.80          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | ~ (v2_pre_topc @ X1)
% 0.59/0.80          | ~ (l1_pre_topc @ X1)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['150', '151'])).
% 0.59/0.80  thf('153', plain,
% 0.59/0.80      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 0.59/0.80        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('154', plain,
% 0.59/0.80      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('155', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('156', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('157', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_funct_1 @ 
% 0.59/0.80           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 0.59/0.80          | (v2_struct_0 @ X1)
% 0.59/0.80          | ~ (v2_pre_topc @ X1)
% 0.59/0.80          | ~ (l1_pre_topc @ X1)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.59/0.80  thf('158', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (v1_funct_1 @ 
% 0.59/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['149', '157'])).
% 0.59/0.80  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('161', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_B)
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (v1_funct_1 @ 
% 0.59/0.80             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 0.59/0.80      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.59/0.80  thf('162', plain,
% 0.59/0.80      (((v1_funct_1 @ 
% 0.59/0.80         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['148', '161'])).
% 0.59/0.80  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('164', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | (v1_funct_1 @ 
% 0.59/0.80           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 0.59/0.80      inference('clc', [status(thm)], ['162', '163'])).
% 0.59/0.80  thf('165', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('166', plain,
% 0.59/0.80      ((v1_funct_1 @ 
% 0.59/0.80        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))),
% 0.59/0.80      inference('clc', [status(thm)], ['164', '165'])).
% 0.59/0.80  thf('167', plain,
% 0.59/0.80      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.80         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.80      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.80  thf('168', plain,
% 0.59/0.80      ((v1_funct_1 @ 
% 0.59/0.80        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.80         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 0.59/0.80      inference('demod', [status(thm)], ['166', '167'])).
% 0.59/0.80  thf('169', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('170', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('171', plain,
% 0.59/0.80      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80        (k1_zfmisc_1 @ 
% 0.59/0.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('demod', [status(thm)], ['123', '124'])).
% 0.59/0.80  thf('172', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.80          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.80          | ~ (l1_pre_topc @ X20)
% 0.59/0.80          | ~ (v2_pre_topc @ X20)
% 0.59/0.80          | (v2_struct_0 @ X20)
% 0.59/0.80          | ~ (l1_pre_topc @ X18)
% 0.59/0.80          | ~ (v2_pre_topc @ X18)
% 0.59/0.80          | (v2_struct_0 @ X18)
% 0.59/0.80          | ~ (v1_funct_1 @ X21)
% 0.59/0.80          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.80          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.80               (k1_zfmisc_1 @ 
% 0.59/0.80                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.80          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.59/0.80             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.80  thf('173', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_funct_2 @ 
% 0.59/0.80           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.80            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.80           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.80          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.80               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['171', '172'])).
% 0.59/0.81  thf('174', plain,
% 0.59/0.81      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.81        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['128', '129'])).
% 0.59/0.81  thf('175', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.81      inference('demod', [status(thm)], ['131', '132'])).
% 0.59/0.81  thf('176', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('178', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_funct_2 @ 
% 0.59/0.81           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('demod', [status(thm)], ['173', '174', '175', '176', '177'])).
% 0.59/0.81  thf('179', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_2 @ 
% 0.59/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['170', '178'])).
% 0.59/0.81  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('182', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_2 @ 
% 0.59/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.59/0.81  thf('183', plain,
% 0.59/0.81      (((v1_funct_2 @ 
% 0.59/0.81         (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81          (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['169', '182'])).
% 0.59/0.81  thf('184', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('185', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v1_funct_2 @ 
% 0.59/0.81           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('clc', [status(thm)], ['183', '184'])).
% 0.59/0.81  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('187', plain,
% 0.59/0.81      ((v1_funct_2 @ 
% 0.59/0.81        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('clc', [status(thm)], ['185', '186'])).
% 0.59/0.81  thf('188', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81             (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             X0)
% 0.59/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) = (X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['147', '168', '187'])).
% 0.59/0.81  thf('189', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('190', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('191', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v2_struct_0 @ X0)
% 0.59/0.81          | ~ (v2_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.81          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X1)))
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.81          | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['40', '77', '78'])).
% 0.59/0.81  thf('192', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 0.59/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['190', '191'])).
% 0.59/0.81  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('194', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('195', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 0.59/0.81          | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.59/0.81  thf('196', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))
% 0.59/0.81        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['189', '195'])).
% 0.59/0.81  thf('197', plain,
% 0.59/0.81      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.81         sk_E)
% 0.59/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 0.59/0.81      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.59/0.81  thf('198', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('199', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.59/0.81  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('201', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)))),
% 0.59/0.81      inference('clc', [status(thm)], ['199', '200'])).
% 0.59/0.81  thf('202', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('203', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81         = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['201', '202'])).
% 0.59/0.81  thf('204', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81         = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['201', '202'])).
% 0.59/0.81  thf('205', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81             (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 0.59/0.81             X0)
% 0.59/0.81          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) = (X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['188', '203', '204'])).
% 0.59/0.81  thf('206', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_D)
% 0.59/0.81        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 0.59/0.81        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81             (k1_zfmisc_1 @ 
% 0.59/0.81              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)
% 0.59/0.81            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['120', '205'])).
% 0.59/0.81  thf('207', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('208', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('209', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_F @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('210', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.81          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.81          | ~ (l1_pre_topc @ X20)
% 0.59/0.81          | ~ (v2_pre_topc @ X20)
% 0.59/0.81          | (v2_struct_0 @ X20)
% 0.59/0.81          | ~ (l1_pre_topc @ X18)
% 0.59/0.81          | ~ (v2_pre_topc @ X18)
% 0.59/0.81          | (v2_struct_0 @ X18)
% 0.59/0.81          | ~ (v1_funct_1 @ X21)
% 0.59/0.81          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.81          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.81          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.81  thf('211', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 0.59/0.81          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['209', '210'])).
% 0.59/0.81  thf('212', plain,
% 0.59/0.81      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('213', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('214', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('215', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('216', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('demod', [status(thm)], ['211', '212', '213', '214', '215'])).
% 0.59/0.81  thf('217', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['208', '216'])).
% 0.59/0.81  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('219', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('220', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 0.59/0.81      inference('demod', [status(thm)], ['217', '218', '219'])).
% 0.59/0.81  thf('221', plain,
% 0.59/0.81      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['207', '220'])).
% 0.59/0.81  thf('222', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('223', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 0.59/0.81      inference('clc', [status(thm)], ['221', '222'])).
% 0.59/0.81  thf('224', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('225', plain,
% 0.59/0.81      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))),
% 0.59/0.81      inference('clc', [status(thm)], ['223', '224'])).
% 0.59/0.81  thf('226', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('227', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.81          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 0.59/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.81          | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.81  thf('228', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81               sk_F @ (u1_struct_0 @ sk_E)))
% 0.59/0.81        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['226', '227'])).
% 0.59/0.81  thf('229', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['2', '17'])).
% 0.59/0.81  thf('230', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_D)
% 0.59/0.81          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 0.59/0.81              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81                 sk_F @ (u1_struct_0 @ X0)))
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.81          | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)],
% 0.59/0.81                ['59', '60', '61', '62', '63', '64', '65'])).
% 0.59/0.81  thf('231', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 0.59/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81               sk_F @ (u1_struct_0 @ sk_E)))
% 0.59/0.81        | (v2_struct_0 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['229', '230'])).
% 0.59/0.81  thf('232', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('233', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_D)
% 0.59/0.81        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 0.59/0.81            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.81               sk_F @ (u1_struct_0 @ sk_E))))),
% 0.59/0.81      inference('clc', [status(thm)], ['231', '232'])).
% 0.59/0.81  thf('234', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('235', plain,
% 0.59/0.81      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 0.59/0.81         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 0.59/0.81            (u1_struct_0 @ sk_E)))),
% 0.59/0.81      inference('clc', [status(thm)], ['233', '234'])).
% 0.59/0.81  thf('236', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['2', '17'])).
% 0.59/0.81  thf('237', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['228', '235', '236'])).
% 0.59/0.81  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('239', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 0.59/0.81      inference('clc', [status(thm)], ['237', '238'])).
% 0.59/0.81  thf('240', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('241', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('242', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('demod', [status(thm)], ['225', '241'])).
% 0.59/0.81  thf('243', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('244', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('245', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_F @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('246', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.81          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.81          | ~ (l1_pre_topc @ X20)
% 0.59/0.81          | ~ (v2_pre_topc @ X20)
% 0.59/0.81          | (v2_struct_0 @ X20)
% 0.59/0.81          | ~ (l1_pre_topc @ X18)
% 0.59/0.81          | ~ (v2_pre_topc @ X18)
% 0.59/0.81          | (v2_struct_0 @ X18)
% 0.59/0.81          | ~ (v1_funct_1 @ X21)
% 0.59/0.81          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.81          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.81          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.59/0.81             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.81  thf('247', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['245', '246'])).
% 0.59/0.81  thf('248', plain,
% 0.59/0.81      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('249', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('250', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('251', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('252', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('demod', [status(thm)], ['247', '248', '249', '250', '251'])).
% 0.59/0.81  thf('253', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['244', '252'])).
% 0.59/0.81  thf('254', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('255', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('256', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.59/0.81  thf('257', plain,
% 0.59/0.81      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['243', '256'])).
% 0.59/0.81  thf('258', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('259', plain,
% 0.59/0.81      (((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['257', '258'])).
% 0.59/0.81  thf('260', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('261', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('clc', [status(thm)], ['259', '260'])).
% 0.59/0.81  thf('262', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('263', plain,
% 0.59/0.81      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('clc', [status(thm)], ['261', '262'])).
% 0.59/0.81  thf('264', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('265', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('266', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_F @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('267', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.81          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.81          | ~ (l1_pre_topc @ X20)
% 0.59/0.81          | ~ (v2_pre_topc @ X20)
% 0.59/0.81          | (v2_struct_0 @ X20)
% 0.59/0.81          | ~ (l1_pre_topc @ X18)
% 0.59/0.81          | ~ (v2_pre_topc @ X18)
% 0.59/0.81          | (v2_struct_0 @ X18)
% 0.59/0.81          | ~ (v1_funct_1 @ X21)
% 0.59/0.81          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.59/0.81          | ~ (m1_subset_1 @ X21 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.59/0.81          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.59/0.81             (k1_zfmisc_1 @ 
% 0.59/0.81              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.81  thf('268', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81           (k1_zfmisc_1 @ 
% 0.59/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['266', '267'])).
% 0.59/0.81  thf('269', plain,
% 0.59/0.81      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('270', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('271', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('272', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('273', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81           (k1_zfmisc_1 @ 
% 0.59/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (v2_pre_topc @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.81      inference('demod', [status(thm)], ['268', '269', '270', '271', '272'])).
% 0.59/0.81  thf('274', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81             (k1_zfmisc_1 @ 
% 0.59/0.81              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['265', '273'])).
% 0.59/0.81  thf('275', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('276', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('277', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 0.59/0.81             (k1_zfmisc_1 @ 
% 0.59/0.81              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.81      inference('demod', [status(thm)], ['274', '275', '276'])).
% 0.59/0.81  thf('278', plain,
% 0.59/0.81      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (k1_zfmisc_1 @ 
% 0.59/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['264', '277'])).
% 0.59/0.81  thf('279', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('280', plain,
% 0.59/0.81      (((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81         (k1_zfmisc_1 @ 
% 0.59/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.59/0.81        | (v2_struct_0 @ sk_A)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['278', '279'])).
% 0.59/0.81  thf('281', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('282', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81           (k1_zfmisc_1 @ 
% 0.59/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.81      inference('clc', [status(thm)], ['280', '281'])).
% 0.59/0.81  thf('283', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('284', plain,
% 0.59/0.81      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('clc', [status(thm)], ['282', '283'])).
% 0.59/0.81  thf('285', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_D)
% 0.59/0.81        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)
% 0.59/0.81            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 0.59/0.81      inference('demod', [status(thm)], ['206', '242', '263', '284'])).
% 0.59/0.81  thf('286', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['2', '17'])).
% 0.59/0.81  thf('287', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('288', plain,
% 0.59/0.81      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.59/0.81  thf(t89_tmap_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.81             ( l1_pre_topc @ B ) ) =>
% 0.59/0.81           ( ![C:$i]:
% 0.59/0.81             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.81               ( ![D:$i]:
% 0.59/0.81                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.81                   ( ![E:$i]:
% 0.59/0.81                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.81                         ( v1_funct_2 @
% 0.59/0.81                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.81                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.59/0.81                         ( m1_subset_1 @
% 0.59/0.81                           E @ 
% 0.59/0.81                           ( k1_zfmisc_1 @
% 0.59/0.81                             ( k2_zfmisc_1 @
% 0.59/0.81                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.81                       ( ( m1_pre_topc @ D @ C ) =>
% 0.59/0.81                         ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.59/0.81                           ( v1_funct_2 @
% 0.59/0.81                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.59/0.81                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.81                           ( v5_pre_topc @
% 0.59/0.81                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 0.59/0.81                           ( m1_subset_1 @
% 0.59/0.81                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.59/0.81                             ( k1_zfmisc_1 @
% 0.59/0.81                               ( k2_zfmisc_1 @
% 0.59/0.81                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf('289', plain,
% 0.59/0.81      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.81         ((v2_struct_0 @ X30)
% 0.59/0.81          | ~ (v2_pre_topc @ X30)
% 0.59/0.81          | ~ (l1_pre_topc @ X30)
% 0.59/0.81          | (v2_struct_0 @ X31)
% 0.59/0.81          | ~ (m1_pre_topc @ X31 @ X32)
% 0.59/0.81          | ~ (m1_pre_topc @ X31 @ X33)
% 0.59/0.81          | (v5_pre_topc @ (k3_tmap_1 @ X32 @ X30 @ X33 @ X31 @ X34) @ X31 @ 
% 0.59/0.81             X30)
% 0.59/0.81          | ~ (m1_subset_1 @ X34 @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X30))))
% 0.59/0.81          | ~ (v5_pre_topc @ X34 @ X33 @ X30)
% 0.59/0.81          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X30))
% 0.59/0.81          | ~ (v1_funct_1 @ X34)
% 0.59/0.81          | ~ (m1_pre_topc @ X33 @ X32)
% 0.59/0.81          | (v2_struct_0 @ X33)
% 0.59/0.81          | ~ (l1_pre_topc @ X32)
% 0.59/0.81          | ~ (v2_pre_topc @ X32)
% 0.59/0.81          | (v2_struct_0 @ X32))),
% 0.59/0.81      inference('cnf', [status(esa)], [t89_tmap_1])).
% 0.59/0.81  thf('290', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v2_struct_0 @ X0)
% 0.59/0.81          | ~ (v2_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | (v2_struct_0 @ sk_C)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.81          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.81               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.81          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_C @ 
% 0.59/0.81               sk_B)
% 0.59/0.81          | (v5_pre_topc @ 
% 0.59/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             X1 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['288', '289'])).
% 0.59/0.81  thf('291', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.81      inference('demod', [status(thm)], ['131', '132'])).
% 0.59/0.81  thf('292', plain,
% 0.59/0.81      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 0.59/0.81        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['128', '129'])).
% 0.59/0.81  thf('293', plain,
% 0.59/0.81      ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_C @ 
% 0.59/0.81        sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('294', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 0.59/0.81      inference('clc', [status(thm)], ['75', '76'])).
% 0.59/0.81  thf('295', plain,
% 0.59/0.81      ((v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_C @ sk_B)),
% 0.59/0.81      inference('demod', [status(thm)], ['293', '294'])).
% 0.59/0.81  thf('296', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('297', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('298', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v2_struct_0 @ X0)
% 0.59/0.81          | ~ (v2_pre_topc @ X0)
% 0.59/0.81          | ~ (l1_pre_topc @ X0)
% 0.59/0.81          | (v2_struct_0 @ sk_C)
% 0.59/0.81          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.81          | (v5_pre_topc @ 
% 0.59/0.81             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             X1 @ sk_B)
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.59/0.81          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.81          | (v2_struct_0 @ X1)
% 0.59/0.81          | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)],
% 0.59/0.81                ['290', '291', '292', '295', '296', '297'])).
% 0.59/0.81  thf('299', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ X0)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.81          | (v5_pre_topc @ 
% 0.59/0.81             (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             X0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_C)
% 0.59/0.81          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.81          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.81          | (v2_struct_0 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['287', '298'])).
% 0.59/0.81  thf('300', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.81      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.81  thf('301', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.81  thf('302', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ X0)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.81          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.59/0.81          | (v5_pre_topc @ 
% 0.59/0.81             (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 0.59/0.81              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81             X0 @ sk_B)
% 0.59/0.81          | (v2_struct_0 @ sk_C)
% 0.59/0.81          | (v2_struct_0 @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['299', '300', '301'])).
% 0.59/0.81  thf('303', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_D)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v5_pre_topc @ 
% 0.59/0.81           (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 0.59/0.81           sk_E @ sk_B)
% 0.59/0.81        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['286', '302'])).
% 0.59/0.81  thf('304', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 0.59/0.81         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 0.59/0.81         = (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['116', '117'])).
% 0.59/0.81  thf('305', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('306', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_D)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v5_pre_topc @ 
% 0.59/0.81           (k2_tmap_1 @ sk_C @ sk_B @ 
% 0.59/0.81            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 0.59/0.81           sk_E @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['303', '304', '305'])).
% 0.59/0.81  thf('307', plain,
% 0.59/0.81      (((v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_D)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_D))),
% 0.59/0.81      inference('sup+', [status(thm)], ['285', '306'])).
% 0.59/0.81  thf('308', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_B)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_D)
% 0.59/0.81        | (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B))),
% 0.59/0.81      inference('simplify', [status(thm)], ['307'])).
% 0.59/0.81  thf('309', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 0.59/0.81        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.59/0.81        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81             sk_E @ sk_B)
% 0.59/0.81        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81             (k1_zfmisc_1 @ 
% 0.59/0.81              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('310', plain,
% 0.59/0.81      ((~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81           sk_E @ sk_B))
% 0.59/0.81         <= (~
% 0.59/0.81             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               sk_E @ sk_B)))),
% 0.59/0.81      inference('split', [status(esa)], ['309'])).
% 0.59/0.81  thf('311', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('312', plain,
% 0.59/0.81      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B))
% 0.59/0.81         <= (~
% 0.59/0.81             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               sk_E @ sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)], ['310', '311'])).
% 0.59/0.81  thf('313', plain,
% 0.59/0.81      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 0.59/0.81      inference('clc', [status(thm)], ['261', '262'])).
% 0.59/0.81  thf('314', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('315', plain,
% 0.59/0.81      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.59/0.81         <= (~
% 0.59/0.81             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('split', [status(esa)], ['309'])).
% 0.59/0.81  thf('316', plain,
% 0.59/0.81      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.59/0.81         <= (~
% 0.59/0.81             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['314', '315'])).
% 0.59/0.81  thf('317', plain,
% 0.59/0.81      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['313', '316'])).
% 0.59/0.81  thf('318', plain,
% 0.59/0.81      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))),
% 0.59/0.81      inference('clc', [status(thm)], ['223', '224'])).
% 0.59/0.81  thf('319', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))
% 0.59/0.81         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))))),
% 0.59/0.81      inference('split', [status(esa)], ['309'])).
% 0.59/0.81  thf('320', plain,
% 0.59/0.81      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['318', '319'])).
% 0.59/0.81  thf('321', plain,
% 0.59/0.81      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81        (k1_zfmisc_1 @ 
% 0.59/0.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.81      inference('clc', [status(thm)], ['282', '283'])).
% 0.59/0.81  thf('322', plain,
% 0.59/0.81      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 0.59/0.81         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['239', '240'])).
% 0.59/0.81  thf('323', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81           (k1_zfmisc_1 @ 
% 0.59/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.59/0.81      inference('split', [status(esa)], ['309'])).
% 0.59/0.81  thf('324', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 0.59/0.81           (k1_zfmisc_1 @ 
% 0.59/0.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81               (k1_zfmisc_1 @ 
% 0.59/0.81                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['322', '323'])).
% 0.59/0.81  thf('325', plain,
% 0.59/0.81      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (k1_zfmisc_1 @ 
% 0.59/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['321', '324'])).
% 0.59/0.81  thf('326', plain,
% 0.59/0.81      (~
% 0.59/0.81       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 0.59/0.81         sk_B)) | 
% 0.59/0.81       ~
% 0.59/0.81       ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (k1_zfmisc_1 @ 
% 0.59/0.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.59/0.81       ~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))) | 
% 0.59/0.81       ~
% 0.59/0.81       ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.81         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.81      inference('split', [status(esa)], ['309'])).
% 0.59/0.81  thf('327', plain,
% 0.59/0.81      (~
% 0.59/0.81       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 0.59/0.81         sk_B))),
% 0.59/0.81      inference('sat_resolution*', [status(thm)], ['317', '320', '325', '326'])).
% 0.59/0.81  thf('328', plain,
% 0.59/0.81      (~ (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B)),
% 0.59/0.81      inference('simpl_trail', [status(thm)], ['312', '327'])).
% 0.59/0.81  thf('329', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_D)
% 0.59/0.81        | (v2_struct_0 @ sk_E)
% 0.59/0.81        | (v2_struct_0 @ sk_C)
% 0.59/0.81        | (v2_struct_0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['308', '328'])).
% 0.59/0.81  thf('330', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('331', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['329', '330'])).
% 0.59/0.81  thf('332', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('333', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.59/0.81      inference('clc', [status(thm)], ['331', '332'])).
% 0.59/0.81  thf('334', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('335', plain, ((v2_struct_0 @ sk_E)),
% 0.59/0.81      inference('clc', [status(thm)], ['333', '334'])).
% 0.59/0.81  thf('336', plain, ($false), inference('demod', [status(thm)], ['0', '335'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
