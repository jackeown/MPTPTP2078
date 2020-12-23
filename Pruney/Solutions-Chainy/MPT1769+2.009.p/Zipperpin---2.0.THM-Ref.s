%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wN7Z13Safw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:10 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 939 expanded)
%              Number of leaves         :   35 ( 275 expanded)
%              Depth                    :   19
%              Number of atoms          : 1851 (44370 expanded)
%              Number of equality atoms :   52 ( 570 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t80_tmap_1,conjecture,(
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
                         => ! [G: $i] :
                              ( ( ( v1_funct_1 @ G )
                                & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( D = A )
                                  & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                               => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( ( D = A )
                                    & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                                 => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                  <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tmap_1])).

thf('0',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X29 )
      | ( ( k3_tmap_1 @ X28 @ X26 @ X29 @ X27 @ X30 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) @ X30 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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
    inference(demod,[status(thm)],['14','15','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k2_tmap_1 @ X24 @ X22 @ X25 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( X16 = X20 )
      | ~ ( r1_funct_2 @ X17 @ X18 @ X21 @ X19 @ X16 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    r1_tarski @ sk_G @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_G @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_G ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_G @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ sk_G @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_G @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','85'])).

thf('87',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','98'])).

thf('100',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r1_tarski @ X0 @ sk_E )
      | ( X0 = sk_E ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_E = sk_G )
    | ( sk_G = sk_E )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['86','101'])).

thf('103',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['103','107'])).

thf('109',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['52','108'])).

thf('110',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['104'])).

thf('112',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('115',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['102'])).

thf('116',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['104'])).

thf('123',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['110','121','122'])).

thf('124',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['109','123'])).

thf('125',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','124'])).

thf('126',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['110','121'])).

thf('127',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wN7Z13Safw
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.44/1.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.66  % Solved by: fo/fo7.sh
% 1.44/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.66  % done 1530 iterations in 1.197s
% 1.44/1.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.66  % SZS output start Refutation
% 1.44/1.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.44/1.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.66  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.44/1.66  thf(sk_D_type, type, sk_D: $i).
% 1.44/1.66  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.44/1.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.44/1.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.66  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.44/1.66  thf(sk_E_type, type, sk_E: $i).
% 1.44/1.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.44/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.44/1.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.44/1.66  thf(sk_F_type, type, sk_F: $i).
% 1.44/1.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.44/1.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.66  thf(sk_G_type, type, sk_G: $i).
% 1.44/1.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.44/1.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.44/1.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.44/1.66  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.44/1.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.44/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.44/1.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.44/1.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.44/1.66  thf(t80_tmap_1, conjecture,
% 1.44/1.66    (![A:$i]:
% 1.44/1.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.66       ( ![B:$i]:
% 1.44/1.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.44/1.66             ( l1_pre_topc @ B ) ) =>
% 1.44/1.66           ( ![C:$i]:
% 1.44/1.66             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.44/1.66               ( ![D:$i]:
% 1.44/1.66                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.44/1.66                   ( ![E:$i]:
% 1.44/1.66                     ( ( ( v1_funct_1 @ E ) & 
% 1.44/1.66                         ( v1_funct_2 @
% 1.44/1.66                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                         ( m1_subset_1 @
% 1.44/1.66                           E @ 
% 1.44/1.66                           ( k1_zfmisc_1 @
% 1.44/1.66                             ( k2_zfmisc_1 @
% 1.44/1.66                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                       ( ![F:$i]:
% 1.44/1.66                         ( ( ( v1_funct_1 @ F ) & 
% 1.44/1.66                             ( v1_funct_2 @
% 1.44/1.66                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                             ( m1_subset_1 @
% 1.44/1.66                               F @ 
% 1.44/1.66                               ( k1_zfmisc_1 @
% 1.44/1.66                                 ( k2_zfmisc_1 @
% 1.44/1.66                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                           ( ![G:$i]:
% 1.44/1.66                             ( ( ( v1_funct_1 @ G ) & 
% 1.44/1.66                                 ( v1_funct_2 @
% 1.44/1.66                                   G @ ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                   ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                                 ( m1_subset_1 @
% 1.44/1.66                                   G @ 
% 1.44/1.66                                   ( k1_zfmisc_1 @
% 1.44/1.66                                     ( k2_zfmisc_1 @
% 1.44/1.66                                       ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                               ( ( ( ( D ) = ( A ) ) & 
% 1.44/1.66                                   ( r1_funct_2 @
% 1.44/1.66                                     ( u1_struct_0 @ A ) @ 
% 1.44/1.66                                     ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                     ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.44/1.66                                 ( ( r2_funct_2 @
% 1.44/1.66                                     ( u1_struct_0 @ C ) @ 
% 1.44/1.66                                     ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.44/1.66                                   ( r2_funct_2 @
% 1.44/1.66                                     ( u1_struct_0 @ C ) @ 
% 1.44/1.66                                     ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.44/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.66    (~( ![A:$i]:
% 1.44/1.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.44/1.66            ( l1_pre_topc @ A ) ) =>
% 1.44/1.66          ( ![B:$i]:
% 1.44/1.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.44/1.66                ( l1_pre_topc @ B ) ) =>
% 1.44/1.66              ( ![C:$i]:
% 1.44/1.66                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.44/1.66                  ( ![D:$i]:
% 1.44/1.66                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.44/1.66                      ( ![E:$i]:
% 1.44/1.66                        ( ( ( v1_funct_1 @ E ) & 
% 1.44/1.66                            ( v1_funct_2 @
% 1.44/1.66                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                            ( m1_subset_1 @
% 1.44/1.66                              E @ 
% 1.44/1.66                              ( k1_zfmisc_1 @
% 1.44/1.66                                ( k2_zfmisc_1 @
% 1.44/1.66                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                          ( ![F:$i]:
% 1.44/1.66                            ( ( ( v1_funct_1 @ F ) & 
% 1.44/1.66                                ( v1_funct_2 @
% 1.44/1.66                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                                ( m1_subset_1 @
% 1.44/1.66                                  F @ 
% 1.44/1.66                                  ( k1_zfmisc_1 @
% 1.44/1.66                                    ( k2_zfmisc_1 @
% 1.44/1.66                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                              ( ![G:$i]:
% 1.44/1.66                                ( ( ( v1_funct_1 @ G ) & 
% 1.44/1.66                                    ( v1_funct_2 @
% 1.44/1.66                                      G @ ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                      ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                                    ( m1_subset_1 @
% 1.44/1.66                                      G @ 
% 1.44/1.66                                      ( k1_zfmisc_1 @
% 1.44/1.66                                        ( k2_zfmisc_1 @
% 1.44/1.66                                          ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                                  ( ( ( ( D ) = ( A ) ) & 
% 1.44/1.66                                      ( r1_funct_2 @
% 1.44/1.66                                        ( u1_struct_0 @ A ) @ 
% 1.44/1.66                                        ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                        ( u1_struct_0 @ D ) @ 
% 1.44/1.66                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.44/1.66                                    ( ( r2_funct_2 @
% 1.44/1.66                                        ( u1_struct_0 @ C ) @ 
% 1.44/1.66                                        ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.44/1.66                                      ( r2_funct_2 @
% 1.44/1.66                                        ( u1_struct_0 @ C ) @ 
% 1.44/1.66                                        ( u1_struct_0 @ B ) @ 
% 1.44/1.66                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.44/1.66    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.44/1.66  thf('0', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 1.44/1.66        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('1', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 1.44/1.66      inference('split', [status(esa)], ['0'])).
% 1.44/1.66  thf('2', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('3', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 1.44/1.66      inference('demod', [status(thm)], ['1', '2'])).
% 1.44/1.66  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('5', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['4', '5'])).
% 1.44/1.66  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('8', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['7', '8'])).
% 1.44/1.66  thf('10', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_E @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('11', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('12', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_E @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('demod', [status(thm)], ['10', '11'])).
% 1.44/1.66  thf(d5_tmap_1, axiom,
% 1.44/1.66    (![A:$i]:
% 1.44/1.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.66       ( ![B:$i]:
% 1.44/1.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.44/1.66             ( l1_pre_topc @ B ) ) =>
% 1.44/1.66           ( ![C:$i]:
% 1.44/1.66             ( ( m1_pre_topc @ C @ A ) =>
% 1.44/1.66               ( ![D:$i]:
% 1.44/1.66                 ( ( m1_pre_topc @ D @ A ) =>
% 1.44/1.66                   ( ![E:$i]:
% 1.44/1.66                     ( ( ( v1_funct_1 @ E ) & 
% 1.44/1.66                         ( v1_funct_2 @
% 1.44/1.66                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                         ( m1_subset_1 @
% 1.44/1.66                           E @ 
% 1.44/1.66                           ( k1_zfmisc_1 @
% 1.44/1.66                             ( k2_zfmisc_1 @
% 1.44/1.66                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66                       ( ( m1_pre_topc @ D @ C ) =>
% 1.44/1.66                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.44/1.66                           ( k2_partfun1 @
% 1.44/1.66                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.44/1.66                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.44/1.66  thf('13', plain,
% 1.44/1.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.44/1.66         ((v2_struct_0 @ X26)
% 1.44/1.66          | ~ (v2_pre_topc @ X26)
% 1.44/1.66          | ~ (l1_pre_topc @ X26)
% 1.44/1.66          | ~ (m1_pre_topc @ X27 @ X28)
% 1.44/1.66          | ~ (m1_pre_topc @ X27 @ X29)
% 1.44/1.66          | ((k3_tmap_1 @ X28 @ X26 @ X29 @ X27 @ X30)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26) @ 
% 1.44/1.66                 X30 @ (u1_struct_0 @ X27)))
% 1.44/1.66          | ~ (m1_subset_1 @ X30 @ 
% 1.44/1.66               (k1_zfmisc_1 @ 
% 1.44/1.66                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))))
% 1.44/1.66          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))
% 1.44/1.66          | ~ (v1_funct_1 @ X30)
% 1.44/1.66          | ~ (m1_pre_topc @ X29 @ X28)
% 1.44/1.66          | ~ (l1_pre_topc @ X28)
% 1.44/1.66          | ~ (v2_pre_topc @ X28)
% 1.44/1.66          | (v2_struct_0 @ X28))),
% 1.44/1.66      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.44/1.66  thf('14', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         ((v2_struct_0 @ X0)
% 1.44/1.66          | ~ (v2_pre_topc @ X0)
% 1.44/1.66          | ~ (l1_pre_topc @ X0)
% 1.44/1.66          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.44/1.66          | ~ (v1_funct_1 @ sk_E)
% 1.44/1.66          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.44/1.66          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X1)))
% 1.44/1.66          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.44/1.66          | ~ (m1_pre_topc @ X1 @ X0)
% 1.44/1.66          | ~ (l1_pre_topc @ sk_B)
% 1.44/1.66          | ~ (v2_pre_topc @ sk_B)
% 1.44/1.66          | (v2_struct_0 @ sk_B))),
% 1.44/1.66      inference('sup-', [status(thm)], ['12', '13'])).
% 1.44/1.66  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('16', plain,
% 1.44/1.66      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('17', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('18', plain,
% 1.44/1.66      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.44/1.66      inference('demod', [status(thm)], ['16', '17'])).
% 1.44/1.66  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('21', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         ((v2_struct_0 @ X0)
% 1.44/1.66          | ~ (v2_pre_topc @ X0)
% 1.44/1.66          | ~ (l1_pre_topc @ X0)
% 1.44/1.66          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.44/1.66          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X1)))
% 1.44/1.66          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.44/1.66          | ~ (m1_pre_topc @ X1 @ X0)
% 1.44/1.66          | (v2_struct_0 @ sk_B))),
% 1.44/1.66      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 1.44/1.66  thf('22', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((v2_struct_0 @ sk_B)
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X0)))
% 1.44/1.66          | ~ (l1_pre_topc @ sk_D)
% 1.44/1.66          | ~ (v2_pre_topc @ sk_D)
% 1.44/1.66          | (v2_struct_0 @ sk_D))),
% 1.44/1.66      inference('sup-', [status(thm)], ['9', '21'])).
% 1.44/1.66  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('24', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('25', plain, ((l1_pre_topc @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['23', '24'])).
% 1.44/1.66  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('27', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['26', '27'])).
% 1.44/1.66  thf('29', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((v2_struct_0 @ sk_B)
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X0)))
% 1.44/1.66          | (v2_struct_0 @ sk_D))),
% 1.44/1.66      inference('demod', [status(thm)], ['22', '25', '28'])).
% 1.44/1.66  thf('30', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((v2_struct_0 @ sk_D)
% 1.44/1.66          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X0)))
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | (v2_struct_0 @ sk_B))),
% 1.44/1.66      inference('simplify', [status(thm)], ['29'])).
% 1.44/1.66  thf('31', plain,
% 1.44/1.66      (((v2_struct_0 @ sk_B)
% 1.44/1.66        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 1.44/1.66            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.44/1.66        | (v2_struct_0 @ sk_D))),
% 1.44/1.66      inference('sup-', [status(thm)], ['6', '30'])).
% 1.44/1.66  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('33', plain,
% 1.44/1.66      (((v2_struct_0 @ sk_D)
% 1.44/1.66        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 1.44/1.66            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.44/1.66      inference('clc', [status(thm)], ['31', '32'])).
% 1.44/1.66  thf('34', plain, (~ (v2_struct_0 @ sk_D)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('35', plain,
% 1.44/1.66      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 1.44/1.66         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.44/1.66            (u1_struct_0 @ sk_C_1)))),
% 1.44/1.66      inference('clc', [status(thm)], ['33', '34'])).
% 1.44/1.66  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['4', '5'])).
% 1.44/1.66  thf('37', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_E @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('demod', [status(thm)], ['10', '11'])).
% 1.44/1.66  thf(d4_tmap_1, axiom,
% 1.44/1.66    (![A:$i]:
% 1.44/1.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.44/1.66       ( ![B:$i]:
% 1.44/1.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.44/1.66             ( l1_pre_topc @ B ) ) =>
% 1.44/1.66           ( ![C:$i]:
% 1.44/1.66             ( ( ( v1_funct_1 @ C ) & 
% 1.44/1.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.44/1.66                 ( m1_subset_1 @
% 1.44/1.66                   C @ 
% 1.44/1.66                   ( k1_zfmisc_1 @
% 1.44/1.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.44/1.66               ( ![D:$i]:
% 1.44/1.66                 ( ( m1_pre_topc @ D @ A ) =>
% 1.44/1.66                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.44/1.66                     ( k2_partfun1 @
% 1.44/1.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.44/1.66                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.44/1.66  thf('38', plain,
% 1.44/1.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.44/1.66         ((v2_struct_0 @ X22)
% 1.44/1.66          | ~ (v2_pre_topc @ X22)
% 1.44/1.66          | ~ (l1_pre_topc @ X22)
% 1.44/1.66          | ~ (m1_pre_topc @ X23 @ X24)
% 1.44/1.66          | ((k2_tmap_1 @ X24 @ X22 @ X25 @ X23)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 1.44/1.66                 X25 @ (u1_struct_0 @ X23)))
% 1.44/1.66          | ~ (m1_subset_1 @ X25 @ 
% 1.44/1.66               (k1_zfmisc_1 @ 
% 1.44/1.66                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 1.44/1.66          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 1.44/1.66          | ~ (v1_funct_1 @ X25)
% 1.44/1.66          | ~ (l1_pre_topc @ X24)
% 1.44/1.66          | ~ (v2_pre_topc @ X24)
% 1.44/1.66          | (v2_struct_0 @ X24))),
% 1.44/1.66      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.44/1.66  thf('39', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((v2_struct_0 @ sk_D)
% 1.44/1.66          | ~ (v2_pre_topc @ sk_D)
% 1.44/1.66          | ~ (l1_pre_topc @ sk_D)
% 1.44/1.66          | ~ (v1_funct_1 @ sk_E)
% 1.44/1.66          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.44/1.66          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X0)))
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | ~ (l1_pre_topc @ sk_B)
% 1.44/1.66          | ~ (v2_pre_topc @ sk_B)
% 1.44/1.66          | (v2_struct_0 @ sk_B))),
% 1.44/1.66      inference('sup-', [status(thm)], ['37', '38'])).
% 1.44/1.66  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['26', '27'])).
% 1.44/1.66  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 1.44/1.66      inference('demod', [status(thm)], ['23', '24'])).
% 1.44/1.66  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('43', plain,
% 1.44/1.66      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.44/1.66      inference('demod', [status(thm)], ['16', '17'])).
% 1.44/1.66  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('46', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((v2_struct_0 @ sk_D)
% 1.44/1.66          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.44/1.66              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66                 sk_E @ (u1_struct_0 @ X0)))
% 1.44/1.66          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.44/1.66          | (v2_struct_0 @ sk_B))),
% 1.44/1.66      inference('demod', [status(thm)],
% 1.44/1.66                ['39', '40', '41', '42', '43', '44', '45'])).
% 1.44/1.66  thf('47', plain,
% 1.44/1.66      (((v2_struct_0 @ sk_B)
% 1.44/1.66        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 1.44/1.66            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.44/1.66        | (v2_struct_0 @ sk_D))),
% 1.44/1.66      inference('sup-', [status(thm)], ['36', '46'])).
% 1.44/1.66  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('49', plain,
% 1.44/1.66      (((v2_struct_0 @ sk_D)
% 1.44/1.66        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 1.44/1.66            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.44/1.66      inference('clc', [status(thm)], ['47', '48'])).
% 1.44/1.66  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('51', plain,
% 1.44/1.66      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 1.44/1.66         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.44/1.66            (u1_struct_0 @ sk_C_1)))),
% 1.44/1.66      inference('clc', [status(thm)], ['49', '50'])).
% 1.44/1.66  thf('52', plain,
% 1.44/1.66      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 1.44/1.66         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 1.44/1.66      inference('sup+', [status(thm)], ['35', '51'])).
% 1.44/1.66  thf('53', plain,
% 1.44/1.66      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('54', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('55', plain,
% 1.44/1.66      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.44/1.66      inference('demod', [status(thm)], ['53', '54'])).
% 1.44/1.66  thf('56', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_E @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('demod', [status(thm)], ['10', '11'])).
% 1.44/1.66  thf(redefinition_r1_funct_2, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.44/1.66     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.44/1.66         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.44/1.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.44/1.66         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.44/1.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.44/1.66       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.44/1.66  thf('57', plain,
% 1.44/1.66      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.44/1.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.44/1.66          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 1.44/1.66          | ~ (v1_funct_1 @ X16)
% 1.44/1.66          | (v1_xboole_0 @ X19)
% 1.44/1.66          | (v1_xboole_0 @ X18)
% 1.44/1.66          | ~ (v1_funct_1 @ X20)
% 1.44/1.66          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 1.44/1.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.44/1.66          | ((X16) = (X20))
% 1.44/1.66          | ~ (r1_funct_2 @ X17 @ X18 @ X21 @ X19 @ X16 @ X20))),
% 1.44/1.66      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.44/1.66  thf('58', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.44/1.66             X1 @ sk_E @ X0)
% 1.44/1.66          | ((sk_E) = (X0))
% 1.44/1.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.44/1.66          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.44/1.66          | ~ (v1_funct_1 @ X0)
% 1.44/1.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66          | (v1_xboole_0 @ X1)
% 1.44/1.66          | ~ (v1_funct_1 @ sk_E)
% 1.44/1.66          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['56', '57'])).
% 1.44/1.66  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('60', plain,
% 1.44/1.66      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.44/1.66      inference('demod', [status(thm)], ['16', '17'])).
% 1.44/1.66  thf('61', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.44/1.66             X1 @ sk_E @ X0)
% 1.44/1.66          | ((sk_E) = (X0))
% 1.44/1.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.44/1.66          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.44/1.66          | ~ (v1_funct_1 @ X0)
% 1.44/1.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66          | (v1_xboole_0 @ X1))),
% 1.44/1.66      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.44/1.66  thf('62', plain,
% 1.44/1.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66        | ~ (v1_funct_1 @ sk_G)
% 1.44/1.66        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.44/1.66        | ~ (m1_subset_1 @ sk_G @ 
% 1.44/1.66             (k1_zfmisc_1 @ 
% 1.44/1.66              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.44/1.66        | ((sk_E) = (sk_G)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['55', '61'])).
% 1.44/1.66  thf('63', plain, ((v1_funct_1 @ sk_G)),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('64', plain,
% 1.44/1.66      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('65', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_G @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('66', plain,
% 1.44/1.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.44/1.66        | ((sk_E) = (sk_G)))),
% 1.44/1.66      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 1.44/1.66  thf('67', plain,
% 1.44/1.66      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.44/1.66      inference('simplify', [status(thm)], ['66'])).
% 1.44/1.66  thf(d10_xboole_0, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.44/1.66  thf('68', plain,
% 1.44/1.66      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.44/1.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.66  thf('69', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.44/1.66      inference('simplify', [status(thm)], ['68'])).
% 1.44/1.66  thf(t3_subset, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.44/1.66  thf('70', plain,
% 1.44/1.66      (![X7 : $i, X9 : $i]:
% 1.44/1.66         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.44/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.66  thf('71', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['69', '70'])).
% 1.44/1.66  thf(cc4_relset_1, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( v1_xboole_0 @ A ) =>
% 1.44/1.66       ( ![C:$i]:
% 1.44/1.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.44/1.66           ( v1_xboole_0 @ C ) ) ) ))).
% 1.44/1.66  thf('72', plain,
% 1.44/1.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.44/1.66         (~ (v1_xboole_0 @ X13)
% 1.44/1.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 1.44/1.66          | (v1_xboole_0 @ X14))),
% 1.44/1.66      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.44/1.66  thf('73', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['71', '72'])).
% 1.44/1.66  thf(d3_tarski, axiom,
% 1.44/1.66    (![A:$i,B:$i]:
% 1.44/1.66     ( ( r1_tarski @ A @ B ) <=>
% 1.44/1.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.44/1.66  thf('74', plain,
% 1.44/1.66      (![X1 : $i, X3 : $i]:
% 1.44/1.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.44/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.66  thf('75', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_G @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('76', plain,
% 1.44/1.66      (![X7 : $i, X8 : $i]:
% 1.44/1.66         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.66  thf('77', plain,
% 1.44/1.66      ((r1_tarski @ sk_G @ 
% 1.44/1.66        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['75', '76'])).
% 1.44/1.66  thf('78', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r2_hidden @ X0 @ X1)
% 1.44/1.66          | (r2_hidden @ X0 @ X2)
% 1.44/1.66          | ~ (r1_tarski @ X1 @ X2))),
% 1.44/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.66  thf('79', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r2_hidden @ X0 @ 
% 1.44/1.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.44/1.66          | ~ (r2_hidden @ X0 @ sk_G))),
% 1.44/1.66      inference('sup-', [status(thm)], ['77', '78'])).
% 1.44/1.66  thf('80', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r1_tarski @ sk_G @ X0)
% 1.44/1.66          | (r2_hidden @ (sk_C @ X0 @ sk_G) @ 
% 1.44/1.66             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['74', '79'])).
% 1.44/1.66  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['69', '70'])).
% 1.44/1.66  thf(t5_subset, axiom,
% 1.44/1.66    (![A:$i,B:$i,C:$i]:
% 1.44/1.66     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.44/1.66          ( v1_xboole_0 @ C ) ) ))).
% 1.44/1.66  thf('82', plain,
% 1.44/1.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.44/1.66         (~ (r2_hidden @ X10 @ X11)
% 1.44/1.66          | ~ (v1_xboole_0 @ X12)
% 1.44/1.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t5_subset])).
% 1.44/1.66  thf('83', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['81', '82'])).
% 1.44/1.66  thf('84', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r1_tarski @ sk_G @ X0)
% 1.44/1.66          | ~ (v1_xboole_0 @ 
% 1.44/1.66               (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['80', '83'])).
% 1.44/1.66  thf('85', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (r1_tarski @ sk_G @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['73', '84'])).
% 1.44/1.66  thf('86', plain, (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_G @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['67', '85'])).
% 1.44/1.66  thf('87', plain,
% 1.44/1.66      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.44/1.66      inference('simplify', [status(thm)], ['66'])).
% 1.44/1.66  thf('88', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]:
% 1.44/1.66         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['71', '72'])).
% 1.44/1.66  thf('89', plain,
% 1.44/1.66      (![X1 : $i, X3 : $i]:
% 1.44/1.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.44/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.66  thf('90', plain,
% 1.44/1.66      ((m1_subset_1 @ sk_E @ 
% 1.44/1.66        (k1_zfmisc_1 @ 
% 1.44/1.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('demod', [status(thm)], ['10', '11'])).
% 1.44/1.66  thf('91', plain,
% 1.44/1.66      (![X7 : $i, X8 : $i]:
% 1.44/1.66         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.44/1.66      inference('cnf', [status(esa)], [t3_subset])).
% 1.44/1.66  thf('92', plain,
% 1.44/1.66      ((r1_tarski @ sk_E @ 
% 1.44/1.66        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['90', '91'])).
% 1.44/1.66  thf('93', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.66         (~ (r2_hidden @ X0 @ X1)
% 1.44/1.66          | (r2_hidden @ X0 @ X2)
% 1.44/1.66          | ~ (r1_tarski @ X1 @ X2))),
% 1.44/1.66      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.66  thf('94', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r2_hidden @ X0 @ 
% 1.44/1.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.44/1.66          | ~ (r2_hidden @ X0 @ sk_E))),
% 1.44/1.66      inference('sup-', [status(thm)], ['92', '93'])).
% 1.44/1.66  thf('95', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r1_tarski @ sk_E @ X0)
% 1.44/1.66          | (r2_hidden @ (sk_C @ X0 @ sk_E) @ 
% 1.44/1.66             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['89', '94'])).
% 1.44/1.66  thf('96', plain,
% 1.44/1.66      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['81', '82'])).
% 1.44/1.66  thf('97', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         ((r1_tarski @ sk_E @ X0)
% 1.44/1.66          | ~ (v1_xboole_0 @ 
% 1.44/1.66               (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.44/1.66      inference('sup-', [status(thm)], ['95', '96'])).
% 1.44/1.66  thf('98', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (r1_tarski @ sk_E @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['88', '97'])).
% 1.44/1.66  thf('99', plain, (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_E @ X0))),
% 1.44/1.66      inference('sup-', [status(thm)], ['87', '98'])).
% 1.44/1.66  thf('100', plain,
% 1.44/1.66      (![X4 : $i, X6 : $i]:
% 1.44/1.66         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.44/1.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.66  thf('101', plain,
% 1.44/1.66      (![X0 : $i]:
% 1.44/1.66         (((sk_E) = (sk_G)) | ~ (r1_tarski @ X0 @ sk_E) | ((X0) = (sk_E)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['99', '100'])).
% 1.44/1.66  thf('102', plain,
% 1.44/1.66      ((((sk_E) = (sk_G)) | ((sk_G) = (sk_E)) | ((sk_E) = (sk_G)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['86', '101'])).
% 1.44/1.66  thf('103', plain, (((sk_E) = (sk_G))),
% 1.44/1.66      inference('simplify', [status(thm)], ['102'])).
% 1.44/1.66  thf('104', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 1.44/1.66        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('105', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('split', [status(esa)], ['104'])).
% 1.44/1.66  thf('106', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('107', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('demod', [status(thm)], ['105', '106'])).
% 1.44/1.66  thf('108', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('sup+', [status(thm)], ['103', '107'])).
% 1.44/1.66  thf('109', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('sup+', [status(thm)], ['52', '108'])).
% 1.44/1.66  thf('110', plain,
% 1.44/1.66      (~
% 1.44/1.66       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)) | 
% 1.44/1.66       ~
% 1.44/1.66       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.44/1.66      inference('split', [status(esa)], ['0'])).
% 1.44/1.66  thf('111', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 1.44/1.66      inference('split', [status(esa)], ['104'])).
% 1.44/1.66  thf('112', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('113', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 1.44/1.66      inference('demod', [status(thm)], ['111', '112'])).
% 1.44/1.66  thf('114', plain,
% 1.44/1.66      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 1.44/1.66         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 1.44/1.66      inference('sup+', [status(thm)], ['35', '51'])).
% 1.44/1.66  thf('115', plain, (((sk_E) = (sk_G))),
% 1.44/1.66      inference('simplify', [status(thm)], ['102'])).
% 1.44/1.66  thf('116', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('split', [status(esa)], ['0'])).
% 1.44/1.66  thf('117', plain, (((sk_D) = (sk_A))),
% 1.44/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.66  thf('118', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('demod', [status(thm)], ['116', '117'])).
% 1.44/1.66  thf('119', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['115', '118'])).
% 1.44/1.66  thf('120', plain,
% 1.44/1.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.44/1.66      inference('sup-', [status(thm)], ['114', '119'])).
% 1.44/1.66  thf('121', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 1.44/1.66       ~
% 1.44/1.66       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 1.44/1.66      inference('sup-', [status(thm)], ['113', '120'])).
% 1.44/1.66  thf('122', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 1.44/1.66       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 1.44/1.66      inference('split', [status(esa)], ['104'])).
% 1.44/1.66  thf('123', plain,
% 1.44/1.66      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.44/1.66      inference('sat_resolution*', [status(thm)], ['110', '121', '122'])).
% 1.44/1.66  thf('124', plain,
% 1.44/1.66      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66        (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F)),
% 1.44/1.66      inference('simpl_trail', [status(thm)], ['109', '123'])).
% 1.44/1.66  thf('125', plain,
% 1.44/1.66      (($false)
% 1.44/1.66         <= (~
% 1.44/1.66             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 1.44/1.66      inference('demod', [status(thm)], ['3', '124'])).
% 1.44/1.66  thf('126', plain,
% 1.44/1.66      (~
% 1.44/1.66       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.44/1.66         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 1.44/1.66      inference('sat_resolution*', [status(thm)], ['110', '121'])).
% 1.44/1.66  thf('127', plain, ($false),
% 1.44/1.66      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 1.44/1.66  
% 1.44/1.66  % SZS output end Refutation
% 1.44/1.66  
% 1.44/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
