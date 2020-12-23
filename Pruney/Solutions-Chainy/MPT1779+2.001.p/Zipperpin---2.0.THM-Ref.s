%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RJpJQ7ZcIv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:39 EST 2020

% Result     : Theorem 6.93s
% Output     : Refutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  429 (3889 expanded)
%              Number of leaves         :   32 (1136 expanded)
%              Depth                    :   29
%              Number of atoms          : 5959 (255178 expanded)
%              Number of equality atoms :   85 ( 445 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_pre_topc @ X35 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_tmap_1,axiom,(
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

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X31 @ ( k3_tmap_1 @ X29 @ X27 @ X30 @ X28 @ X32 ) ) @ ( k3_tmap_1 @ X29 @ X27 @ X30 @ X31 @ X32 ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_tmap_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_E @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('36',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('38',plain,(
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

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('48',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

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
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_E @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
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

thf('94',plain,(
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
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
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
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('116',plain,(
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
    inference(demod,[status(thm)],['99','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('119',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','120'])).

thf('122',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
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

thf('125',plain,(
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
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('128',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('134',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','131','136','137','138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('148',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('149',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','89','155','156'])).

thf('158',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('160',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('161',plain,(
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

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
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
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('170',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('171',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['158','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('179',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

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

thf('180',plain,(
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

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('184',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
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

thf('186',plain,(
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
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['183','191'])).

thf('193',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('194',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('195',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['182','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('203',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('206',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
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

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
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
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['205','213'])).

thf('215',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('216',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('217',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['214','215','216','217'])).

thf('219',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['204','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('225',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['181','203','225'])).

thf('227',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('229',plain,(
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
    inference(demod,[status(thm)],['99','114','115'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('232',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('233',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['227','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('242',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ X0 )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['226','242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference('sup-',[status(thm)],['157','244'])).

thf('246',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('247',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('248',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
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

thf('250',plain,(
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
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251','252','253','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['247','255'])).

thf('257',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('258',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('259',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['246','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('267',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('269',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('270',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
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

thf('272',plain,(
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
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['272','273','274','275','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['269','277'])).

thf('279',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('280',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('281',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['278','279','280','281'])).

thf('283',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['268','282'])).

thf('284',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['283','284'])).

thf('286',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('289',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('291',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('292',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
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

thf('294',plain,(
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
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['294','295','296','297','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['291','299'])).

thf('301',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('302',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('303',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('304',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['300','301','302','303'])).

thf('305',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['290','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('311',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference(demod,[status(thm)],['245','267','289','311'])).

thf('313',plain,(
    m1_pre_topc @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ) )).

thf('315',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v5_pre_topc @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X23 @ X24 @ X22 @ X25 ) @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('316',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('318',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135'])).

thf('319',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['316','317','318','319','320','321','322','323'])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F ) @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['313','324'])).

thf('326',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('327',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C ) @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('328',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['312','327'])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B ) ),
    inference(simplify,[status(thm)],['328'])).

thf('330',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['330'])).

thf('332',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['294','295','296','297','298'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['335','336','337'])).

thf('339',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['332','338'])).

thf('340',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['339','340'])).

thf('342',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['341','342'])).

thf('344',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['330'])).

thf('345',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251','252','253','254'])).

thf('349',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('353',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['346','352'])).

thf('354',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['353','354'])).

thf('356',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['355','356'])).

thf('358',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['330'])).

thf('359',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['272','273','274','275','276'])).

thf('363',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['363','364','365'])).

thf('367',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['360','366'])).

thf('368',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['367','368'])).

thf('370',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['369','370'])).

thf('372',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['330'])).

thf('373',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['371','372'])).

thf('374',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['330'])).

thf('375',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['345','359','373','374'])).

thf('376',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F ) @ sk_E @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['331','375'])).

thf('377',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('379',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('381',plain,(
    m1_pre_topc @ sk_E @ sk_D ),
    inference('sup-',[status(thm)],['2','17'])).

thf('382',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['379','380','381'])).

thf('383',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ) ),
    inference(clc,[status(thm)],['382','383'])).

thf('385',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) ),
    inference(clc,[status(thm)],['384','385'])).

thf('387',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['376','386'])).

thf('388',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['329','387'])).

thf('389',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['390','391'])).

thf('393',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['392','393'])).

thf('395',plain,(
    $false ),
    inference(demod,[status(thm)],['0','394'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RJpJQ7ZcIv
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 6.93/7.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.93/7.15  % Solved by: fo/fo7.sh
% 6.93/7.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.93/7.15  % done 9338 iterations in 6.668s
% 6.93/7.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.93/7.15  % SZS output start Refutation
% 6.93/7.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.93/7.15  thf(sk_C_type, type, sk_C: $i).
% 6.93/7.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.93/7.15  thf(sk_B_type, type, sk_B: $i).
% 6.93/7.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.93/7.15  thf(sk_A_type, type, sk_A: $i).
% 6.93/7.15  thf(sk_E_type, type, sk_E: $i).
% 6.93/7.15  thf(sk_F_type, type, sk_F: $i).
% 6.93/7.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.93/7.15  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 6.93/7.15  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 6.93/7.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.93/7.15  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 6.93/7.15  thf(sk_D_type, type, sk_D: $i).
% 6.93/7.15  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 6.93/7.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.93/7.15  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.93/7.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.93/7.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.93/7.15  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 6.93/7.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.93/7.15  thf(t90_tmap_1, conjecture,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]:
% 6.93/7.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.93/7.15             ( l1_pre_topc @ B ) ) =>
% 6.93/7.15           ( ![C:$i]:
% 6.93/7.15             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.93/7.15               ( ![D:$i]:
% 6.93/7.15                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.93/7.15                   ( ![E:$i]:
% 6.93/7.15                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 6.93/7.15                       ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 6.93/7.15                         ( ![F:$i]:
% 6.93/7.15                           ( ( ( v1_funct_1 @ F ) & 
% 6.93/7.15                               ( v1_funct_2 @
% 6.93/7.15                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                               ( m1_subset_1 @
% 6.93/7.15                                 F @ 
% 6.93/7.15                                 ( k1_zfmisc_1 @
% 6.93/7.15                                   ( k2_zfmisc_1 @
% 6.93/7.15                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                             ( ( ( v1_funct_1 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 6.93/7.15                                 ( v1_funct_2 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 6.93/7.15                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                                 ( v5_pre_topc @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 6.93/7.15                                 ( m1_subset_1 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 6.93/7.15                                   ( k1_zfmisc_1 @
% 6.93/7.15                                     ( k2_zfmisc_1 @
% 6.93/7.15                                       ( u1_struct_0 @ C ) @ 
% 6.93/7.15                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                               ( ( v1_funct_1 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 6.93/7.15                                 ( v1_funct_2 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 6.93/7.15                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                                 ( v5_pre_topc @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 6.93/7.15                                 ( m1_subset_1 @
% 6.93/7.15                                   ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 6.93/7.15                                   ( k1_zfmisc_1 @
% 6.93/7.15                                     ( k2_zfmisc_1 @
% 6.93/7.15                                       ( u1_struct_0 @ E ) @ 
% 6.93/7.15                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.93/7.15  thf(zf_stmt_0, negated_conjecture,
% 6.93/7.15    (~( ![A:$i]:
% 6.93/7.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.93/7.15            ( l1_pre_topc @ A ) ) =>
% 6.93/7.15          ( ![B:$i]:
% 6.93/7.15            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.93/7.15                ( l1_pre_topc @ B ) ) =>
% 6.93/7.15              ( ![C:$i]:
% 6.93/7.15                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.93/7.15                  ( ![D:$i]:
% 6.93/7.15                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.93/7.15                      ( ![E:$i]:
% 6.93/7.15                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 6.93/7.15                          ( ( ( m1_pre_topc @ C @ D ) & ( m1_pre_topc @ E @ C ) ) =>
% 6.93/7.15                            ( ![F:$i]:
% 6.93/7.15                              ( ( ( v1_funct_1 @ F ) & 
% 6.93/7.15                                  ( v1_funct_2 @
% 6.93/7.15                                    F @ ( u1_struct_0 @ D ) @ 
% 6.93/7.15                                    ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                                  ( m1_subset_1 @
% 6.93/7.15                                    F @ 
% 6.93/7.15                                    ( k1_zfmisc_1 @
% 6.93/7.15                                      ( k2_zfmisc_1 @
% 6.93/7.15                                        ( u1_struct_0 @ D ) @ 
% 6.93/7.15                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                                ( ( ( v1_funct_1 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) ) & 
% 6.93/7.15                                    ( v1_funct_2 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 6.93/7.15                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                                    ( v5_pre_topc @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ C @ B ) & 
% 6.93/7.15                                    ( m1_subset_1 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ C @ F ) @ 
% 6.93/7.15                                      ( k1_zfmisc_1 @
% 6.93/7.15                                        ( k2_zfmisc_1 @
% 6.93/7.15                                          ( u1_struct_0 @ C ) @ 
% 6.93/7.15                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                                  ( ( v1_funct_1 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) ) & 
% 6.93/7.15                                    ( v1_funct_2 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 6.93/7.15                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                                    ( v5_pre_topc @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ E @ B ) & 
% 6.93/7.15                                    ( m1_subset_1 @
% 6.93/7.15                                      ( k3_tmap_1 @ A @ B @ D @ E @ F ) @ 
% 6.93/7.15                                      ( k1_zfmisc_1 @
% 6.93/7.15                                        ( k2_zfmisc_1 @
% 6.93/7.15                                          ( u1_struct_0 @ E ) @ 
% 6.93/7.15                                          ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 6.93/7.15    inference('cnf.neg', [status(esa)], [t90_tmap_1])).
% 6.93/7.15  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('2', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(t7_tsep_1, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]:
% 6.93/7.15         ( ( m1_pre_topc @ B @ A ) =>
% 6.93/7.15           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 6.93/7.15  thf('4', plain,
% 6.93/7.15      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X33 @ X34)
% 6.93/7.15          | (m1_pre_topc @ X35 @ X34)
% 6.93/7.15          | ~ (m1_pre_topc @ X35 @ X33)
% 6.93/7.15          | ~ (l1_pre_topc @ X34)
% 6.93/7.15          | ~ (v2_pre_topc @ X34))),
% 6.93/7.15      inference('cnf', [status(esa)], [t7_tsep_1])).
% 6.93/7.15  thf('5', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (m1_pre_topc @ X0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['3', '4'])).
% 6.93/7.15  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(cc1_pre_topc, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 6.93/7.15  thf('7', plain,
% 6.93/7.15      (![X4 : $i, X5 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X4 @ X5)
% 6.93/7.15          | (v2_pre_topc @ X4)
% 6.93/7.15          | ~ (l1_pre_topc @ X5)
% 6.93/7.15          | ~ (v2_pre_topc @ X5))),
% 6.93/7.15      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 6.93/7.15  thf('8', plain,
% 6.93/7.15      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['6', '7'])).
% 6.93/7.15  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('11', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(dt_m1_pre_topc, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( l1_pre_topc @ A ) =>
% 6.93/7.15       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 6.93/7.15  thf('13', plain,
% 6.93/7.15      (![X6 : $i, X7 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.93/7.15  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['12', '13'])).
% 6.93/7.15  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('17', plain,
% 6.93/7.15      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_C) | (m1_pre_topc @ X0 @ sk_D))),
% 6.93/7.15      inference('demod', [status(thm)], ['5', '11', '16'])).
% 6.93/7.15  thf('18', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf(t2_tsep_1, axiom,
% 6.93/7.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 6.93/7.15  thf('19', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('20', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(t79_tmap_1, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]:
% 6.93/7.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.93/7.15             ( l1_pre_topc @ B ) ) =>
% 6.93/7.15           ( ![C:$i]:
% 6.93/7.15             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.93/7.15               ( ![D:$i]:
% 6.93/7.15                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.93/7.15                   ( ![E:$i]:
% 6.93/7.15                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 6.93/7.15                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 6.93/7.15                         ( ![F:$i]:
% 6.93/7.15                           ( ( ( v1_funct_1 @ F ) & 
% 6.93/7.15                               ( v1_funct_2 @
% 6.93/7.15                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                               ( m1_subset_1 @
% 6.93/7.15                                 F @ 
% 6.93/7.15                                 ( k1_zfmisc_1 @
% 6.93/7.15                                   ( k2_zfmisc_1 @
% 6.93/7.15                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                             ( r2_funct_2 @
% 6.93/7.15                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 6.93/7.15                               ( k3_tmap_1 @
% 6.93/7.15                                 A @ B @ D @ E @ 
% 6.93/7.15                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 6.93/7.15                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.93/7.15  thf('21', plain,
% 6.93/7.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X27)
% 6.93/7.15          | ~ (v2_pre_topc @ X27)
% 6.93/7.15          | ~ (l1_pre_topc @ X27)
% 6.93/7.15          | (v2_struct_0 @ X28)
% 6.93/7.15          | ~ (m1_pre_topc @ X28 @ X29)
% 6.93/7.15          | ~ (m1_pre_topc @ X28 @ X30)
% 6.93/7.15          | ~ (m1_pre_topc @ X31 @ X28)
% 6.93/7.15          | ~ (v1_funct_1 @ X32)
% 6.93/7.15          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X27))
% 6.93/7.15          | ~ (m1_subset_1 @ X32 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X27))))
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27) @ 
% 6.93/7.15             (k3_tmap_1 @ X29 @ X27 @ X28 @ X31 @ 
% 6.93/7.15              (k3_tmap_1 @ X29 @ X27 @ X30 @ X28 @ X32)) @ 
% 6.93/7.15             (k3_tmap_1 @ X29 @ X27 @ X30 @ X31 @ X32))
% 6.93/7.15          | ~ (m1_pre_topc @ X31 @ X29)
% 6.93/7.15          | (v2_struct_0 @ X31)
% 6.93/7.15          | ~ (m1_pre_topc @ X30 @ X29)
% 6.93/7.15          | (v2_struct_0 @ X30)
% 6.93/7.15          | ~ (l1_pre_topc @ X29)
% 6.93/7.15          | ~ (v2_pre_topc @ X29)
% 6.93/7.15          | (v2_struct_0 @ X29))),
% 6.93/7.15      inference('cnf', [status(esa)], [t79_tmap_1])).
% 6.93/7.15  thf('22', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F))
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X2)
% 6.93/7.15          | ~ (m1_pre_topc @ X2 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X2 @ X0)
% 6.93/7.15          | (v2_struct_0 @ X2)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['20', '21'])).
% 6.93/7.15  thf('23', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('27', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X2)
% 6.93/7.15          | ~ (m1_pre_topc @ X2 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X2 @ X0)
% 6.93/7.15          | (v2_struct_0 @ X2)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 6.93/7.15  thf('28', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['19', '27'])).
% 6.93/7.15  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('30', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('31', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('32', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 6.93/7.15  thf('33', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X1 @ sk_F))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('simplify', [status(thm)], ['32'])).
% 6.93/7.15  thf('34', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_E @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ 
% 6.93/7.15              (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ sk_E)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['18', '33'])).
% 6.93/7.15  thf('35', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('36', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('37', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(d5_tmap_1, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]:
% 6.93/7.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.93/7.15             ( l1_pre_topc @ B ) ) =>
% 6.93/7.15           ( ![C:$i]:
% 6.93/7.15             ( ( m1_pre_topc @ C @ A ) =>
% 6.93/7.15               ( ![D:$i]:
% 6.93/7.15                 ( ( m1_pre_topc @ D @ A ) =>
% 6.93/7.15                   ( ![E:$i]:
% 6.93/7.15                     ( ( ( v1_funct_1 @ E ) & 
% 6.93/7.15                         ( v1_funct_2 @
% 6.93/7.15                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                         ( m1_subset_1 @
% 6.93/7.15                           E @ 
% 6.93/7.15                           ( k1_zfmisc_1 @
% 6.93/7.15                             ( k2_zfmisc_1 @
% 6.93/7.15                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15                       ( ( m1_pre_topc @ D @ C ) =>
% 6.93/7.15                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 6.93/7.15                           ( k2_partfun1 @
% 6.93/7.15                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 6.93/7.15                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.93/7.15  thf('38', plain,
% 6.93/7.15      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X12)
% 6.93/7.15          | ~ (v2_pre_topc @ X12)
% 6.93/7.15          | ~ (l1_pre_topc @ X12)
% 6.93/7.15          | ~ (m1_pre_topc @ X13 @ X14)
% 6.93/7.15          | ~ (m1_pre_topc @ X13 @ X15)
% 6.93/7.15          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 6.93/7.15                 X16 @ (u1_struct_0 @ X13)))
% 6.93/7.15          | ~ (m1_subset_1 @ X16 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 6.93/7.15          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 6.93/7.15          | ~ (v1_funct_1 @ X16)
% 6.93/7.15          | ~ (m1_pre_topc @ X15 @ X14)
% 6.93/7.15          | ~ (l1_pre_topc @ X14)
% 6.93/7.15          | ~ (v2_pre_topc @ X14)
% 6.93/7.15          | (v2_struct_0 @ X14))),
% 6.93/7.15      inference('cnf', [status(esa)], [d5_tmap_1])).
% 6.93/7.15  thf('39', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['37', '38'])).
% 6.93/7.15  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('41', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('44', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 6.93/7.15  thf('45', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['36', '44'])).
% 6.93/7.15  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('48', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('49', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 6.93/7.15  thf('50', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('simplify', [status(thm)], ['49'])).
% 6.93/7.15  thf('51', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_E)))
% 6.93/7.15        | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['35', '50'])).
% 6.93/7.15  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('53', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_E))))),
% 6.93/7.15      inference('clc', [status(thm)], ['51', '52'])).
% 6.93/7.15  thf('54', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('55', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['53', '54'])).
% 6.93/7.15  thf('56', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('57', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(d4_tmap_1, axiom,
% 6.93/7.15    (![A:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.93/7.15       ( ![B:$i]:
% 6.93/7.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.93/7.15             ( l1_pre_topc @ B ) ) =>
% 6.93/7.15           ( ![C:$i]:
% 6.93/7.15             ( ( ( v1_funct_1 @ C ) & 
% 6.93/7.15                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15                 ( m1_subset_1 @
% 6.93/7.15                   C @ 
% 6.93/7.15                   ( k1_zfmisc_1 @
% 6.93/7.15                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15               ( ![D:$i]:
% 6.93/7.15                 ( ( m1_pre_topc @ D @ A ) =>
% 6.93/7.15                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 6.93/7.15                     ( k2_partfun1 @
% 6.93/7.15                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 6.93/7.15                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 6.93/7.15  thf('58', plain,
% 6.93/7.15      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X8)
% 6.93/7.15          | ~ (v2_pre_topc @ X8)
% 6.93/7.15          | ~ (l1_pre_topc @ X8)
% 6.93/7.15          | ~ (m1_pre_topc @ X9 @ X10)
% 6.93/7.15          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 6.93/7.15                 X11 @ (u1_struct_0 @ X9)))
% 6.93/7.15          | ~ (m1_subset_1 @ X11 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 6.93/7.15          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 6.93/7.15          | ~ (v1_funct_1 @ X11)
% 6.93/7.15          | ~ (l1_pre_topc @ X10)
% 6.93/7.15          | ~ (v2_pre_topc @ X10)
% 6.93/7.15          | (v2_struct_0 @ X10))),
% 6.93/7.15      inference('cnf', [status(esa)], [d4_tmap_1])).
% 6.93/7.15  thf('59', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['57', '58'])).
% 6.93/7.15  thf('60', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('62', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('63', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('66', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)],
% 6.93/7.15                ['59', '60', '61', '62', '63', '64', '65'])).
% 6.93/7.15  thf('67', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_E)))
% 6.93/7.15        | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['56', '66'])).
% 6.93/7.15  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('69', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_E))))),
% 6.93/7.15      inference('clc', [status(thm)], ['67', '68'])).
% 6.93/7.15  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('71', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['69', '70'])).
% 6.93/7.15  thf('72', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('sup+', [status(thm)], ['55', '71'])).
% 6.93/7.15  thf('73', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_E @ X0)
% 6.93/7.15          | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_E @ 
% 6.93/7.15              (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)) @ 
% 6.93/7.15             (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 6.93/7.15          | (v2_struct_0 @ sk_E)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('demod', [status(thm)], ['34', '72'])).
% 6.93/7.15  thf('74', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15           (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 6.93/7.15        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['1', '73'])).
% 6.93/7.15  thf('75', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('76', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('simplify', [status(thm)], ['49'])).
% 6.93/7.15  thf('77', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_C)))
% 6.93/7.15        | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['75', '76'])).
% 6.93/7.15  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('79', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_C))))),
% 6.93/7.15      inference('clc', [status(thm)], ['77', '78'])).
% 6.93/7.15  thf('80', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('81', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_C)))),
% 6.93/7.15      inference('clc', [status(thm)], ['79', '80'])).
% 6.93/7.15  thf('82', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('83', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_D)
% 6.93/7.15          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ X0)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)],
% 6.93/7.15                ['59', '60', '61', '62', '63', '64', '65'])).
% 6.93/7.15  thf('84', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_C)))
% 6.93/7.15        | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['82', '83'])).
% 6.93/7.15  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('86', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_C))))),
% 6.93/7.15      inference('clc', [status(thm)], ['84', '85'])).
% 6.93/7.15  thf('87', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('88', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_C)))),
% 6.93/7.15      inference('clc', [status(thm)], ['86', '87'])).
% 6.93/7.15  thf('89', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 6.93/7.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('sup+', [status(thm)], ['81', '88'])).
% 6.93/7.15  thf('90', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('92', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('93', plain,
% 6.93/7.15      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X12)
% 6.93/7.15          | ~ (v2_pre_topc @ X12)
% 6.93/7.15          | ~ (l1_pre_topc @ X12)
% 6.93/7.15          | ~ (m1_pre_topc @ X13 @ X14)
% 6.93/7.15          | ~ (m1_pre_topc @ X13 @ X15)
% 6.93/7.15          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 6.93/7.15                 X16 @ (u1_struct_0 @ X13)))
% 6.93/7.15          | ~ (m1_subset_1 @ X16 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 6.93/7.15          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 6.93/7.15          | ~ (v1_funct_1 @ X16)
% 6.93/7.15          | ~ (m1_pre_topc @ X15 @ X14)
% 6.93/7.15          | ~ (l1_pre_topc @ X14)
% 6.93/7.15          | ~ (v2_pre_topc @ X14)
% 6.93/7.15          | (v2_struct_0 @ X14))),
% 6.93/7.15      inference('cnf', [status(esa)], [d5_tmap_1])).
% 6.93/7.15  thf('94', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X0)
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15                 (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['92', '93'])).
% 6.93/7.15  thf('95', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('96', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('99', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X0)
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15                 (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 6.93/7.15  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('102', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 6.93/7.15  thf('103', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (l1_pre_topc @ sk_A)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_A))),
% 6.93/7.15      inference('sup-', [status(thm)], ['101', '102'])).
% 6.93/7.15  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('106', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | (v2_struct_0 @ sk_A))),
% 6.93/7.15      inference('demod', [status(thm)], ['103', '104', '105'])).
% 6.93/7.15  thf('107', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_A)
% 6.93/7.15        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_C)))
% 6.93/7.15        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['100', '106'])).
% 6.93/7.15  thf('108', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_C)))),
% 6.93/7.15      inference('clc', [status(thm)], ['86', '87'])).
% 6.93/7.15  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('110', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_A)
% 6.93/7.15        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['107', '108', '109'])).
% 6.93/7.15  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('112', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 6.93/7.15      inference('clc', [status(thm)], ['110', '111'])).
% 6.93/7.15  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('114', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('115', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('116', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X0)
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['99', '114', '115'])).
% 6.93/7.15  thf('117', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('sup-', [status(thm)], ['91', '116'])).
% 6.93/7.15  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('119', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('120', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 6.93/7.15          | (v2_struct_0 @ sk_D))),
% 6.93/7.15      inference('demod', [status(thm)], ['117', '118', '119'])).
% 6.93/7.15  thf('121', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))
% 6.93/7.15        | ~ (m1_pre_topc @ sk_E @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['90', '120'])).
% 6.93/7.15  thf('122', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('123', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('124', plain,
% 6.93/7.15      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X8)
% 6.93/7.15          | ~ (v2_pre_topc @ X8)
% 6.93/7.15          | ~ (l1_pre_topc @ X8)
% 6.93/7.15          | ~ (m1_pre_topc @ X9 @ X10)
% 6.93/7.15          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 6.93/7.15                 X11 @ (u1_struct_0 @ X9)))
% 6.93/7.15          | ~ (m1_subset_1 @ X11 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 6.93/7.15          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 6.93/7.15          | ~ (v1_funct_1 @ X11)
% 6.93/7.15          | ~ (l1_pre_topc @ X10)
% 6.93/7.15          | ~ (v2_pre_topc @ X10)
% 6.93/7.15          | (v2_struct_0 @ X10))),
% 6.93/7.15      inference('cnf', [status(esa)], [d4_tmap_1])).
% 6.93/7.15  thf('125', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15                 (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['123', '124'])).
% 6.93/7.15  thf('126', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('127', plain,
% 6.93/7.15      (![X4 : $i, X5 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X4 @ X5)
% 6.93/7.15          | (v2_pre_topc @ X4)
% 6.93/7.15          | ~ (l1_pre_topc @ X5)
% 6.93/7.15          | ~ (v2_pre_topc @ X5))),
% 6.93/7.15      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 6.93/7.15  thf('128', plain,
% 6.93/7.15      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 6.93/7.15      inference('sup-', [status(thm)], ['126', '127'])).
% 6.93/7.15  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('131', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('133', plain,
% 6.93/7.15      (![X6 : $i, X7 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.93/7.15  thf('134', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 6.93/7.15      inference('sup-', [status(thm)], ['132', '133'])).
% 6.93/7.15  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('136', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('137', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('138', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('140', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('141', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_C)
% 6.93/7.15          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15                 (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)],
% 6.93/7.15                ['125', '131', '136', '137', '138', '139', '140'])).
% 6.93/7.15  thf('142', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_E)))
% 6.93/7.15        | (v2_struct_0 @ sk_C))),
% 6.93/7.15      inference('sup-', [status(thm)], ['122', '141'])).
% 6.93/7.15  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('144', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_C)
% 6.93/7.15        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_E))))),
% 6.93/7.15      inference('clc', [status(thm)], ['142', '143'])).
% 6.93/7.15  thf('145', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('146', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15            (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['144', '145'])).
% 6.93/7.15  thf('147', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('148', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('149', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 6.93/7.15         sk_E)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('demod', [status(thm)], ['146', '147', '148'])).
% 6.93/7.15  thf('150', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('151', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['121', '149', '150'])).
% 6.93/7.15  thf('152', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('153', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15            = (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['151', '152'])).
% 6.93/7.15  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('155', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15         = (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E))),
% 6.93/7.15      inference('clc', [status(thm)], ['153', '154'])).
% 6.93/7.15  thf('156', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('157', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15           (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 6.93/7.15           (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['74', '89', '155', '156'])).
% 6.93/7.15  thf('158', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('159', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('160', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(dt_k3_tmap_1, axiom,
% 6.93/7.15    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.93/7.15         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 6.93/7.15         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 6.93/7.15         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 6.93/7.15         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15         ( m1_subset_1 @
% 6.93/7.15           E @ 
% 6.93/7.15           ( k1_zfmisc_1 @
% 6.93/7.15             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.93/7.15       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 6.93/7.15         ( v1_funct_2 @
% 6.93/7.15           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 6.93/7.15           ( u1_struct_0 @ B ) ) & 
% 6.93/7.15         ( m1_subset_1 @
% 6.93/7.15           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 6.93/7.15           ( k1_zfmisc_1 @
% 6.93/7.15             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 6.93/7.15  thf('161', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('162', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((m1_subset_1 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['160', '161'])).
% 6.93/7.15  thf('163', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('164', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('165', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('166', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('167', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((m1_subset_1 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 6.93/7.15  thf('168', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (m1_subset_1 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('sup-', [status(thm)], ['159', '167'])).
% 6.93/7.15  thf('169', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('170', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('171', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('172', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (m1_subset_1 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 6.93/7.15  thf('173', plain,
% 6.93/7.15      (((m1_subset_1 @ 
% 6.93/7.15         (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15         (k1_zfmisc_1 @ 
% 6.93/7.15          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['158', '172'])).
% 6.93/7.15  thf('174', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('175', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (m1_subset_1 @ 
% 6.93/7.15           (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('clc', [status(thm)], ['173', '174'])).
% 6.93/7.15  thf('176', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('177', plain,
% 6.93/7.15      ((m1_subset_1 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('clc', [status(thm)], ['175', '176'])).
% 6.93/7.15  thf('178', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('179', plain,
% 6.93/7.15      ((m1_subset_1 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('demod', [status(thm)], ['177', '178'])).
% 6.93/7.15  thf(redefinition_r2_funct_2, axiom,
% 6.93/7.15    (![A:$i,B:$i,C:$i,D:$i]:
% 6.93/7.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.93/7.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.93/7.15         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.93/7.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.93/7.15       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.93/7.15  thf('180', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.93/7.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.93/7.15          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 6.93/7.15          | ~ (v1_funct_1 @ X0)
% 6.93/7.15          | ~ (v1_funct_1 @ X3)
% 6.93/7.15          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 6.93/7.15          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.93/7.15          | ((X0) = (X3))
% 6.93/7.15          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 6.93/7.15      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 6.93/7.15  thf('181', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 6.93/7.15             X0)
% 6.93/7.15          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) = (X0))
% 6.93/7.15          | ~ (m1_subset_1 @ X0 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ X0)
% 6.93/7.15          | ~ (v1_funct_1 @ 
% 6.93/7.15               (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15                (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))
% 6.93/7.15          | ~ (v1_funct_2 @ 
% 6.93/7.15               (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15                (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 6.93/7.15               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['179', '180'])).
% 6.93/7.15  thf('182', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('183', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('184', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('185', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('186', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_1 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['184', '185'])).
% 6.93/7.15  thf('187', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('188', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('189', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('190', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('191', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_1 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 6.93/7.15  thf('192', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (v1_funct_1 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 6.93/7.15      inference('sup-', [status(thm)], ['183', '191'])).
% 6.93/7.15  thf('193', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('194', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('195', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('196', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (v1_funct_1 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 6.93/7.15      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 6.93/7.15  thf('197', plain,
% 6.93/7.15      (((v1_funct_1 @ 
% 6.93/7.15         (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['182', '196'])).
% 6.93/7.15  thf('198', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('199', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_1 @ 
% 6.93/7.15           (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))))),
% 6.93/7.15      inference('clc', [status(thm)], ['197', '198'])).
% 6.93/7.15  thf('200', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('201', plain,
% 6.93/7.15      ((v1_funct_1 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)))),
% 6.93/7.15      inference('clc', [status(thm)], ['199', '200'])).
% 6.93/7.15  thf('202', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('203', plain,
% 6.93/7.15      ((v1_funct_1 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 6.93/7.15      inference('demod', [status(thm)], ['201', '202'])).
% 6.93/7.15  thf('204', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('205', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('206', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('207', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 6.93/7.15             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('208', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_2 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['206', '207'])).
% 6.93/7.15  thf('209', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('210', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('211', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('213', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_2 @ 
% 6.93/7.15           (k3_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['208', '209', '210', '211', '212'])).
% 6.93/7.15  thf('214', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (v1_funct_2 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['205', '213'])).
% 6.93/7.15  thf('215', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('216', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('217', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('218', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (v1_funct_2 @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('demod', [status(thm)], ['214', '215', '216', '217'])).
% 6.93/7.15  thf('219', plain,
% 6.93/7.15      (((v1_funct_2 @ 
% 6.93/7.15         (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['204', '218'])).
% 6.93/7.15  thf('220', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('221', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_2 @ 
% 6.93/7.15           (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('clc', [status(thm)], ['219', '220'])).
% 6.93/7.15  thf('222', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('223', plain,
% 6.93/7.15      ((v1_funct_2 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)) @ 
% 6.93/7.15        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('clc', [status(thm)], ['221', '222'])).
% 6.93/7.15  thf('224', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('225', plain,
% 6.93/7.15      ((v1_funct_2 @ 
% 6.93/7.15        (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 6.93/7.15        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['223', '224'])).
% 6.93/7.15  thf('226', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) @ 
% 6.93/7.15             X0)
% 6.93/7.15          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)) = (X0))
% 6.93/7.15          | ~ (m1_subset_1 @ X0 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ X0))),
% 6.93/7.15      inference('demod', [status(thm)], ['181', '203', '225'])).
% 6.93/7.15  thf('227', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('228', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('229', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v2_struct_0 @ X0)
% 6.93/7.15          | ~ (v2_pre_topc @ X0)
% 6.93/7.15          | ~ (l1_pre_topc @ X0)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_C @ X0)
% 6.93/7.15          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X1)))
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X1 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['99', '114', '115'])).
% 6.93/7.15  thf('230', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_C))),
% 6.93/7.15      inference('sup-', [status(thm)], ['228', '229'])).
% 6.93/7.15  thf('231', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('232', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('233', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('234', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 6.93/7.15          | (v2_struct_0 @ sk_C))),
% 6.93/7.15      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 6.93/7.15  thf('235', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_C)
% 6.93/7.15          | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ X0 @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ X0)))
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('simplify', [status(thm)], ['234'])).
% 6.93/7.15  thf('236', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))
% 6.93/7.15        | (v2_struct_0 @ sk_C))),
% 6.93/7.15      inference('sup-', [status(thm)], ['227', '235'])).
% 6.93/7.15  thf('237', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('238', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_C)
% 6.93/7.15        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E))))),
% 6.93/7.15      inference('clc', [status(thm)], ['236', '237'])).
% 6.93/7.15  thf('239', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('240', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['238', '239'])).
% 6.93/7.15  thf('241', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 6.93/7.15         sk_E)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('demod', [status(thm)], ['146', '147', '148'])).
% 6.93/7.15  thf('242', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 6.93/7.15         sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 6.93/7.15      inference('sup+', [status(thm)], ['240', '241'])).
% 6.93/7.15  thf('243', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ 
% 6.93/7.15         sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_E @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C)))),
% 6.93/7.15      inference('sup+', [status(thm)], ['240', '241'])).
% 6.93/7.15  thf('244', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (r2_funct_2 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15             (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 6.93/7.15             X0)
% 6.93/7.15          | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15              (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) = (X0))
% 6.93/7.15          | ~ (m1_subset_1 @ X0 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ X0))),
% 6.93/7.15      inference('demod', [status(thm)], ['226', '242', '243'])).
% 6.93/7.15  thf('245', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 6.93/7.15        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 6.93/7.15             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)
% 6.93/7.15            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['157', '244'])).
% 6.93/7.15  thf('246', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('247', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('248', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('249', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('250', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['248', '249'])).
% 6.93/7.15  thf('251', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('252', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('253', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('254', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('255', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['250', '251', '252', '253', '254'])).
% 6.93/7.15  thf('256', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['247', '255'])).
% 6.93/7.15  thf('257', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('258', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('259', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('260', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F)))),
% 6.93/7.15      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 6.93/7.15  thf('261', plain,
% 6.93/7.15      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['246', '260'])).
% 6.93/7.15  thf('262', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('263', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 6.93/7.15      inference('clc', [status(thm)], ['261', '262'])).
% 6.93/7.15  thf('264', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('265', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('clc', [status(thm)], ['263', '264'])).
% 6.93/7.15  thf('266', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('sup+', [status(thm)], ['55', '71'])).
% 6.93/7.15  thf('267', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 6.93/7.15      inference('demod', [status(thm)], ['265', '266'])).
% 6.93/7.15  thf('268', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('269', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('270', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('271', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 6.93/7.15             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('272', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['270', '271'])).
% 6.93/7.15  thf('273', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('274', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('275', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('276', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('277', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['272', '273', '274', '275', '276'])).
% 6.93/7.15  thf('278', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['269', '277'])).
% 6.93/7.15  thf('279', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('280', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('281', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('282', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('demod', [status(thm)], ['278', '279', '280', '281'])).
% 6.93/7.15  thf('283', plain,
% 6.93/7.15      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['268', '282'])).
% 6.93/7.15  thf('284', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('285', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('clc', [status(thm)], ['283', '284'])).
% 6.93/7.15  thf('286', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('287', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('clc', [status(thm)], ['285', '286'])).
% 6.93/7.15  thf('288', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('sup+', [status(thm)], ['55', '71'])).
% 6.93/7.15  thf('289', plain,
% 6.93/7.15      ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 6.93/7.15        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['287', '288'])).
% 6.93/7.15  thf('290', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('291', plain,
% 6.93/7.15      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 6.93/7.15      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.93/7.15  thf('292', plain,
% 6.93/7.15      ((m1_subset_1 @ sk_F @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('293', plain,
% 6.93/7.15      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X17 @ X18)
% 6.93/7.15          | ~ (m1_pre_topc @ X19 @ X18)
% 6.93/7.15          | ~ (l1_pre_topc @ X20)
% 6.93/7.15          | ~ (v2_pre_topc @ X20)
% 6.93/7.15          | (v2_struct_0 @ X20)
% 6.93/7.15          | ~ (l1_pre_topc @ X18)
% 6.93/7.15          | ~ (v2_pre_topc @ X18)
% 6.93/7.15          | (v2_struct_0 @ X18)
% 6.93/7.15          | ~ (v1_funct_1 @ X21)
% 6.93/7.15          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 6.93/7.15          | ~ (m1_subset_1 @ X21 @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 6.93/7.15      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.93/7.15  thf('294', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v1_funct_1 @ sk_F)
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('sup-', [status(thm)], ['292', '293'])).
% 6.93/7.15  thf('295', plain,
% 6.93/7.15      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('296', plain, ((v1_funct_1 @ sk_F)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('297', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('298', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('299', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['294', '295', '296', '297', '298'])).
% 6.93/7.15  thf('300', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_D)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('sup-', [status(thm)], ['291', '299'])).
% 6.93/7.15  thf('301', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('302', plain, ((l1_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['14', '15'])).
% 6.93/7.15  thf('303', plain, ((v2_pre_topc @ sk_D)),
% 6.93/7.15      inference('demod', [status(thm)], ['8', '9', '10'])).
% 6.93/7.15  thf('304', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_D)
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('demod', [status(thm)], ['300', '301', '302', '303'])).
% 6.93/7.15  thf('305', plain,
% 6.93/7.15      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (k1_zfmisc_1 @ 
% 6.93/7.15          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['290', '304'])).
% 6.93/7.15  thf('306', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('307', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('clc', [status(thm)], ['305', '306'])).
% 6.93/7.15  thf('308', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('309', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('clc', [status(thm)], ['307', '308'])).
% 6.93/7.15  thf('310', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('sup+', [status(thm)], ['55', '71'])).
% 6.93/7.15  thf('311', plain,
% 6.93/7.15      ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('demod', [status(thm)], ['309', '310'])).
% 6.93/7.15  thf('312', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | ((k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E)
% 6.93/7.15            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 6.93/7.15      inference('demod', [status(thm)], ['245', '267', '289', '311'])).
% 6.93/7.15  thf('313', plain, ((m1_pre_topc @ sk_E @ sk_C)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('314', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf(fc2_tmap_1, axiom,
% 6.93/7.15    (![A:$i,B:$i,C:$i,D:$i]:
% 6.93/7.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.93/7.15         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 6.93/7.15         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 6.93/7.15         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.93/7.15         ( v5_pre_topc @ C @ A @ B ) & 
% 6.93/7.15         ( m1_subset_1 @
% 6.93/7.15           C @ 
% 6.93/7.15           ( k1_zfmisc_1 @
% 6.93/7.15             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 6.93/7.15         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.93/7.15       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 6.93/7.15         ( v1_funct_2 @
% 6.93/7.15           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 6.93/7.15           ( u1_struct_0 @ B ) ) & 
% 6.93/7.15         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 6.93/7.15  thf('315', plain,
% 6.93/7.15      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 6.93/7.15         (~ (m1_subset_1 @ X22 @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))))
% 6.93/7.15          | ~ (v5_pre_topc @ X22 @ X23 @ X24)
% 6.93/7.15          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 6.93/7.15          | ~ (v1_funct_1 @ X22)
% 6.93/7.15          | ~ (l1_pre_topc @ X24)
% 6.93/7.15          | ~ (v2_pre_topc @ X24)
% 6.93/7.15          | (v2_struct_0 @ X24)
% 6.93/7.15          | ~ (l1_pre_topc @ X23)
% 6.93/7.15          | ~ (v2_pre_topc @ X23)
% 6.93/7.15          | (v2_struct_0 @ X23)
% 6.93/7.15          | (v2_struct_0 @ X25)
% 6.93/7.15          | ~ (m1_pre_topc @ X25 @ X23)
% 6.93/7.15          | (v5_pre_topc @ (k2_tmap_1 @ X23 @ X24 @ X22 @ X25) @ X25 @ X24))),
% 6.93/7.15      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 6.93/7.15  thf('316', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v5_pre_topc @ 
% 6.93/7.15           (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0) @ 
% 6.93/7.15           X0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_C)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_B)
% 6.93/7.15          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))
% 6.93/7.15          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15               sk_C @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['314', '315'])).
% 6.93/7.15  thf('317', plain, ((v2_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['128', '129', '130'])).
% 6.93/7.15  thf('318', plain, ((l1_pre_topc @ sk_C)),
% 6.93/7.15      inference('demod', [status(thm)], ['134', '135'])).
% 6.93/7.15  thf('319', plain, ((v2_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('320', plain, ((l1_pre_topc @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('321', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('322', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('323', plain,
% 6.93/7.15      ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_C @ 
% 6.93/7.15        sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('324', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v5_pre_topc @ 
% 6.93/7.15           (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ X0) @ 
% 6.93/7.15           X0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ X0)
% 6.93/7.15          | (v2_struct_0 @ sk_C)
% 6.93/7.15          | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)],
% 6.93/7.15                ['316', '317', '318', '319', '320', '321', '322', '323'])).
% 6.93/7.15  thf('325', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v5_pre_topc @ 
% 6.93/7.15           (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F) @ sk_E) @ 
% 6.93/7.15           sk_E @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['313', '324'])).
% 6.93/7.15  thf('326', plain,
% 6.93/7.15      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_F)
% 6.93/7.15         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C))),
% 6.93/7.15      inference('clc', [status(thm)], ['112', '113'])).
% 6.93/7.15  thf('327', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v5_pre_topc @ 
% 6.93/7.15           (k2_tmap_1 @ sk_C @ sk_B @ 
% 6.93/7.15            (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_C) @ sk_E) @ 
% 6.93/7.15           sk_E @ sk_B))),
% 6.93/7.15      inference('demod', [status(thm)], ['325', '326'])).
% 6.93/7.15  thf('328', plain,
% 6.93/7.15      (((v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup+', [status(thm)], ['312', '327'])).
% 6.93/7.15  thf('329', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v2_struct_0 @ sk_C)
% 6.93/7.15        | (v2_struct_0 @ sk_E)
% 6.93/7.15        | (v2_struct_0 @ sk_D)
% 6.93/7.15        | (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B))),
% 6.93/7.15      inference('simplify', [status(thm)], ['328'])).
% 6.93/7.15  thf('330', plain,
% 6.93/7.15      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 6.93/7.15        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15             sk_E @ sk_B)
% 6.93/7.15        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('331', plain,
% 6.93/7.15      ((~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           sk_E @ sk_B))
% 6.93/7.15         <= (~
% 6.93/7.15             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15               sk_E @ sk_B)))),
% 6.93/7.15      inference('split', [status(esa)], ['330'])).
% 6.93/7.15  thf('332', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('333', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('334', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['294', '295', '296', '297', '298'])).
% 6.93/7.15  thf('335', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_A)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('sup-', [status(thm)], ['333', '334'])).
% 6.93/7.15  thf('336', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('337', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('338', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (k1_zfmisc_1 @ 
% 6.93/7.15              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('demod', [status(thm)], ['335', '336', '337'])).
% 6.93/7.15  thf('339', plain,
% 6.93/7.15      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (k1_zfmisc_1 @ 
% 6.93/7.15          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 6.93/7.15        | (v2_struct_0 @ sk_A)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['332', '338'])).
% 6.93/7.15  thf('340', plain, (~ (v2_struct_0 @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('341', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('clc', [status(thm)], ['339', '340'])).
% 6.93/7.15  thf('342', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('343', plain,
% 6.93/7.15      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15        (k1_zfmisc_1 @ 
% 6.93/7.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('clc', [status(thm)], ['341', '342'])).
% 6.93/7.15  thf('344', plain,
% 6.93/7.15      ((~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (k1_zfmisc_1 @ 
% 6.93/7.15            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 6.93/7.15         <= (~
% 6.93/7.15             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15               (k1_zfmisc_1 @ 
% 6.93/7.15                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 6.93/7.15      inference('split', [status(esa)], ['330'])).
% 6.93/7.15  thf('345', plain,
% 6.93/7.15      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (k1_zfmisc_1 @ 
% 6.93/7.15          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('sup-', [status(thm)], ['343', '344'])).
% 6.93/7.15  thf('346', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('347', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('348', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['250', '251', '252', '253', '254'])).
% 6.93/7.15  thf('349', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_A)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['347', '348'])).
% 6.93/7.15  thf('350', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('351', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('352', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)))),
% 6.93/7.15      inference('demod', [status(thm)], ['349', '350', '351'])).
% 6.93/7.15  thf('353', plain,
% 6.93/7.15      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))
% 6.93/7.15        | (v2_struct_0 @ sk_A)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['346', '352'])).
% 6.93/7.15  thf('354', plain, (~ (v2_struct_0 @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('355', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 6.93/7.15      inference('clc', [status(thm)], ['353', '354'])).
% 6.93/7.15  thf('356', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('357', plain,
% 6.93/7.15      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))),
% 6.93/7.15      inference('clc', [status(thm)], ['355', '356'])).
% 6.93/7.15  thf('358', plain,
% 6.93/7.15      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))
% 6.93/7.15         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))))),
% 6.93/7.15      inference('split', [status(esa)], ['330'])).
% 6.93/7.15  thf('359', plain,
% 6.93/7.15      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['357', '358'])).
% 6.93/7.15  thf('360', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('361', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('362', plain,
% 6.93/7.15      (![X0 : $i, X1 : $i]:
% 6.93/7.15         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.93/7.15          | (v2_struct_0 @ X1)
% 6.93/7.15          | ~ (v2_pre_topc @ X1)
% 6.93/7.15          | ~ (l1_pre_topc @ X1)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.93/7.15      inference('demod', [status(thm)], ['272', '273', '274', '275', '276'])).
% 6.93/7.15  thf('363', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (l1_pre_topc @ sk_A)
% 6.93/7.15          | ~ (v2_pre_topc @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['361', '362'])).
% 6.93/7.15  thf('364', plain, ((l1_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('365', plain, ((v2_pre_topc @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('366', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | (v2_struct_0 @ sk_B)
% 6.93/7.15          | (v2_struct_0 @ sk_A)
% 6.93/7.15          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F) @ 
% 6.93/7.15             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('demod', [status(thm)], ['363', '364', '365'])).
% 6.93/7.15  thf('367', plain,
% 6.93/7.15      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 6.93/7.15        | (v2_struct_0 @ sk_A)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['360', '366'])).
% 6.93/7.15  thf('368', plain, (~ (v2_struct_0 @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('369', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_B)
% 6.93/7.15        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('clc', [status(thm)], ['367', '368'])).
% 6.93/7.15  thf('370', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('371', plain,
% 6.93/7.15      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 6.93/7.15      inference('clc', [status(thm)], ['369', '370'])).
% 6.93/7.15  thf('372', plain,
% 6.93/7.15      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 6.93/7.15         <= (~
% 6.93/7.15             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 6.93/7.15      inference('split', [status(esa)], ['330'])).
% 6.93/7.15  thf('373', plain,
% 6.93/7.15      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 6.93/7.15      inference('sup-', [status(thm)], ['371', '372'])).
% 6.93/7.15  thf('374', plain,
% 6.93/7.15      (~
% 6.93/7.15       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 6.93/7.15         sk_B)) | 
% 6.93/7.15       ~
% 6.93/7.15       ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 6.93/7.15       ~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F))) | 
% 6.93/7.15       ~
% 6.93/7.15       ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15         (k1_zfmisc_1 @ 
% 6.93/7.15          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 6.93/7.15      inference('split', [status(esa)], ['330'])).
% 6.93/7.15  thf('375', plain,
% 6.93/7.15      (~
% 6.93/7.15       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ sk_E @ 
% 6.93/7.15         sk_B))),
% 6.93/7.15      inference('sat_resolution*', [status(thm)], ['345', '359', '373', '374'])).
% 6.93/7.15  thf('376', plain,
% 6.93/7.15      (~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F) @ 
% 6.93/7.15          sk_E @ sk_B)),
% 6.93/7.15      inference('simpl_trail', [status(thm)], ['331', '375'])).
% 6.93/7.15  thf('377', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.93/7.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.15  thf('378', plain,
% 6.93/7.15      (![X0 : $i]:
% 6.93/7.15         ((v2_struct_0 @ sk_B)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.93/7.15          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.93/7.15          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_F)
% 6.93/7.15              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15                 sk_F @ (u1_struct_0 @ X0)))
% 6.93/7.15          | (v2_struct_0 @ sk_A))),
% 6.93/7.15      inference('demod', [status(thm)], ['103', '104', '105'])).
% 6.93/7.15  thf('379', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_A)
% 6.93/7.15        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.15            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.93/7.15               sk_F @ (u1_struct_0 @ sk_E)))
% 6.93/7.15        | ~ (m1_pre_topc @ sk_E @ sk_D)
% 6.93/7.15        | (v2_struct_0 @ sk_B))),
% 6.93/7.15      inference('sup-', [status(thm)], ['377', '378'])).
% 6.93/7.15  thf('380', plain,
% 6.93/7.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)
% 6.93/7.15         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 6.93/7.15            (u1_struct_0 @ sk_E)))),
% 6.93/7.15      inference('clc', [status(thm)], ['69', '70'])).
% 6.93/7.15  thf('381', plain, ((m1_pre_topc @ sk_E @ sk_D)),
% 6.93/7.15      inference('sup-', [status(thm)], ['2', '17'])).
% 6.93/7.15  thf('382', plain,
% 6.93/7.15      (((v2_struct_0 @ sk_A)
% 6.93/7.16        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.16            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))
% 6.93/7.16        | (v2_struct_0 @ sk_B))),
% 6.93/7.16      inference('demod', [status(thm)], ['379', '380', '381'])).
% 6.93/7.16  thf('383', plain, (~ (v2_struct_0 @ sk_A)),
% 6.93/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.16  thf('384', plain,
% 6.93/7.16      (((v2_struct_0 @ sk_B)
% 6.93/7.16        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.16            = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E)))),
% 6.93/7.16      inference('clc', [status(thm)], ['382', '383'])).
% 6.93/7.16  thf('385', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.16  thf('386', plain,
% 6.93/7.16      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_E @ sk_F)
% 6.93/7.16         = (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E))),
% 6.93/7.16      inference('clc', [status(thm)], ['384', '385'])).
% 6.93/7.16  thf('387', plain,
% 6.93/7.16      (~ (v5_pre_topc @ (k2_tmap_1 @ sk_D @ sk_B @ sk_F @ sk_E) @ sk_E @ sk_B)),
% 6.93/7.16      inference('demod', [status(thm)], ['376', '386'])).
% 6.93/7.16  thf('388', plain,
% 6.93/7.16      (((v2_struct_0 @ sk_D)
% 6.93/7.16        | (v2_struct_0 @ sk_E)
% 6.93/7.16        | (v2_struct_0 @ sk_C)
% 6.93/7.16        | (v2_struct_0 @ sk_B))),
% 6.93/7.16      inference('sup-', [status(thm)], ['329', '387'])).
% 6.93/7.16  thf('389', plain, (~ (v2_struct_0 @ sk_B)),
% 6.93/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.16  thf('390', plain,
% 6.93/7.16      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 6.93/7.16      inference('sup-', [status(thm)], ['388', '389'])).
% 6.93/7.16  thf('391', plain, (~ (v2_struct_0 @ sk_C)),
% 6.93/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.16  thf('392', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 6.93/7.16      inference('clc', [status(thm)], ['390', '391'])).
% 6.93/7.16  thf('393', plain, (~ (v2_struct_0 @ sk_D)),
% 6.93/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.93/7.16  thf('394', plain, ((v2_struct_0 @ sk_E)),
% 6.93/7.16      inference('clc', [status(thm)], ['392', '393'])).
% 6.93/7.16  thf('395', plain, ($false), inference('demod', [status(thm)], ['0', '394'])).
% 6.93/7.16  
% 6.93/7.16  % SZS output end Refutation
% 6.93/7.16  
% 6.93/7.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
