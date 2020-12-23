%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2vJANP8HqJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:10 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 888 expanded)
%              Number of leaves         :   35 ( 260 expanded)
%              Depth                    :   18
%              Number of atoms          : 1795 (44013 expanded)
%              Number of equality atoms :   58 ( 582 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
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
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
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
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_E
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,
    ( ( sk_E = sk_G )
    | ( sk_E
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','83'])).

thf('85',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('87',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    r1_tarski @ sk_G @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('91',plain,
    ( ( sk_G
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_G
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( sk_E = sk_G )
    | ( sk_G
      = ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,
    ( ( sk_G = sk_E )
    | ( sk_E = sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,(
    sk_G = sk_E ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['95','99'])).

thf('101',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['52','100'])).

thf('102',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['96'])).

thf('104',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('107',plain,(
    sk_G = sk_E ),
    inference(simplify,[status(thm)],['94'])).

thf('108',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['96'])).

thf('115',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['102','113','114'])).

thf('116',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['101','115'])).

thf('117',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','116'])).

thf('118',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['102','113'])).

thf('119',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2vJANP8HqJ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.62  % Solved by: fo/fo7.sh
% 1.37/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.62  % done 1453 iterations in 1.167s
% 1.37/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.62  % SZS output start Refutation
% 1.37/1.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.62  thf(sk_E_type, type, sk_E: $i).
% 1.37/1.62  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.37/1.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.37/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.37/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.37/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.62  thf(sk_F_type, type, sk_F: $i).
% 1.37/1.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.37/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.37/1.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.37/1.62  thf(sk_G_type, type, sk_G: $i).
% 1.37/1.62  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.37/1.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.62  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.37/1.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.37/1.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.62  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.37/1.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.37/1.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.37/1.62  thf(t80_tmap_1, conjecture,
% 1.37/1.62    (![A:$i]:
% 1.37/1.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.62       ( ![B:$i]:
% 1.37/1.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.37/1.62             ( l1_pre_topc @ B ) ) =>
% 1.37/1.62           ( ![C:$i]:
% 1.37/1.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.37/1.62               ( ![D:$i]:
% 1.37/1.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.37/1.62                   ( ![E:$i]:
% 1.37/1.62                     ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.62                         ( v1_funct_2 @
% 1.37/1.62                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                         ( m1_subset_1 @
% 1.37/1.62                           E @ 
% 1.37/1.62                           ( k1_zfmisc_1 @
% 1.37/1.62                             ( k2_zfmisc_1 @
% 1.37/1.62                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                       ( ![F:$i]:
% 1.37/1.62                         ( ( ( v1_funct_1 @ F ) & 
% 1.37/1.62                             ( v1_funct_2 @
% 1.37/1.62                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                             ( m1_subset_1 @
% 1.37/1.62                               F @ 
% 1.37/1.62                               ( k1_zfmisc_1 @
% 1.37/1.62                                 ( k2_zfmisc_1 @
% 1.37/1.62                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                           ( ![G:$i]:
% 1.37/1.62                             ( ( ( v1_funct_1 @ G ) & 
% 1.37/1.62                                 ( v1_funct_2 @
% 1.37/1.62                                   G @ ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                   ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                                 ( m1_subset_1 @
% 1.37/1.62                                   G @ 
% 1.37/1.62                                   ( k1_zfmisc_1 @
% 1.37/1.62                                     ( k2_zfmisc_1 @
% 1.37/1.62                                       ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                               ( ( ( ( D ) = ( A ) ) & 
% 1.37/1.62                                   ( r1_funct_2 @
% 1.37/1.62                                     ( u1_struct_0 @ A ) @ 
% 1.37/1.62                                     ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                     ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.37/1.62                                 ( ( r2_funct_2 @
% 1.37/1.62                                     ( u1_struct_0 @ C ) @ 
% 1.37/1.62                                     ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.37/1.62                                   ( r2_funct_2 @
% 1.37/1.62                                     ( u1_struct_0 @ C ) @ 
% 1.37/1.62                                     ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.62    (~( ![A:$i]:
% 1.37/1.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.37/1.62            ( l1_pre_topc @ A ) ) =>
% 1.37/1.62          ( ![B:$i]:
% 1.37/1.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.37/1.62                ( l1_pre_topc @ B ) ) =>
% 1.37/1.62              ( ![C:$i]:
% 1.37/1.62                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.37/1.62                  ( ![D:$i]:
% 1.37/1.62                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.37/1.62                      ( ![E:$i]:
% 1.37/1.62                        ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.62                            ( v1_funct_2 @
% 1.37/1.62                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                            ( m1_subset_1 @
% 1.37/1.62                              E @ 
% 1.37/1.62                              ( k1_zfmisc_1 @
% 1.37/1.62                                ( k2_zfmisc_1 @
% 1.37/1.62                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                          ( ![F:$i]:
% 1.37/1.62                            ( ( ( v1_funct_1 @ F ) & 
% 1.37/1.62                                ( v1_funct_2 @
% 1.37/1.62                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                                ( m1_subset_1 @
% 1.37/1.62                                  F @ 
% 1.37/1.62                                  ( k1_zfmisc_1 @
% 1.37/1.62                                    ( k2_zfmisc_1 @
% 1.37/1.62                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                              ( ![G:$i]:
% 1.37/1.62                                ( ( ( v1_funct_1 @ G ) & 
% 1.37/1.62                                    ( v1_funct_2 @
% 1.37/1.62                                      G @ ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                      ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                                    ( m1_subset_1 @
% 1.37/1.62                                      G @ 
% 1.37/1.62                                      ( k1_zfmisc_1 @
% 1.37/1.62                                        ( k2_zfmisc_1 @
% 1.37/1.62                                          ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                                  ( ( ( ( D ) = ( A ) ) & 
% 1.37/1.62                                      ( r1_funct_2 @
% 1.37/1.62                                        ( u1_struct_0 @ A ) @ 
% 1.37/1.62                                        ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                        ( u1_struct_0 @ D ) @ 
% 1.37/1.62                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.37/1.62                                    ( ( r2_funct_2 @
% 1.37/1.62                                        ( u1_struct_0 @ C ) @ 
% 1.37/1.62                                        ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.37/1.62                                      ( r2_funct_2 @
% 1.37/1.62                                        ( u1_struct_0 @ C ) @ 
% 1.37/1.62                                        ( u1_struct_0 @ B ) @ 
% 1.37/1.62                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.37/1.62    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.37/1.62  thf('0', plain,
% 1.37/1.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 1.37/1.62        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62             (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('1', plain,
% 1.37/1.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.62         <= (~
% 1.37/1.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.37/1.62      inference('split', [status(esa)], ['0'])).
% 1.37/1.62  thf('2', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('3', plain,
% 1.37/1.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.62         <= (~
% 1.37/1.62             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.37/1.62      inference('demod', [status(thm)], ['1', '2'])).
% 1.37/1.62  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('5', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['4', '5'])).
% 1.37/1.62  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('8', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['7', '8'])).
% 1.37/1.62  thf('10', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_E @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('11', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('12', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_E @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.62      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.62  thf(d5_tmap_1, axiom,
% 1.37/1.62    (![A:$i]:
% 1.37/1.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.62       ( ![B:$i]:
% 1.37/1.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.37/1.62             ( l1_pre_topc @ B ) ) =>
% 1.37/1.62           ( ![C:$i]:
% 1.37/1.62             ( ( m1_pre_topc @ C @ A ) =>
% 1.37/1.62               ( ![D:$i]:
% 1.37/1.62                 ( ( m1_pre_topc @ D @ A ) =>
% 1.37/1.62                   ( ![E:$i]:
% 1.37/1.62                     ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.62                         ( v1_funct_2 @
% 1.37/1.62                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                         ( m1_subset_1 @
% 1.37/1.62                           E @ 
% 1.37/1.62                           ( k1_zfmisc_1 @
% 1.37/1.62                             ( k2_zfmisc_1 @
% 1.37/1.62                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62                       ( ( m1_pre_topc @ D @ C ) =>
% 1.37/1.62                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.37/1.62                           ( k2_partfun1 @
% 1.37/1.62                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.37/1.62                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.62  thf('13', plain,
% 1.37/1.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.37/1.62         ((v2_struct_0 @ X26)
% 1.37/1.62          | ~ (v2_pre_topc @ X26)
% 1.37/1.62          | ~ (l1_pre_topc @ X26)
% 1.37/1.62          | ~ (m1_pre_topc @ X27 @ X28)
% 1.37/1.62          | ~ (m1_pre_topc @ X27 @ X29)
% 1.37/1.62          | ((k3_tmap_1 @ X28 @ X26 @ X29 @ X27 @ X30)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26) @ 
% 1.37/1.62                 X30 @ (u1_struct_0 @ X27)))
% 1.37/1.62          | ~ (m1_subset_1 @ X30 @ 
% 1.37/1.62               (k1_zfmisc_1 @ 
% 1.37/1.62                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))))
% 1.37/1.62          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))
% 1.37/1.62          | ~ (v1_funct_1 @ X30)
% 1.37/1.62          | ~ (m1_pre_topc @ X29 @ X28)
% 1.37/1.62          | ~ (l1_pre_topc @ X28)
% 1.37/1.62          | ~ (v2_pre_topc @ X28)
% 1.37/1.62          | (v2_struct_0 @ X28))),
% 1.37/1.62      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.37/1.62  thf('14', plain,
% 1.37/1.62      (![X0 : $i, X1 : $i]:
% 1.37/1.62         ((v2_struct_0 @ X0)
% 1.37/1.62          | ~ (v2_pre_topc @ X0)
% 1.37/1.62          | ~ (l1_pre_topc @ X0)
% 1.37/1.62          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.37/1.62          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.37/1.62               (u1_struct_0 @ sk_B_1))
% 1.37/1.62          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X1)))
% 1.37/1.62          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.37/1.62          | ~ (m1_pre_topc @ X1 @ X0)
% 1.37/1.62          | ~ (l1_pre_topc @ sk_B_1)
% 1.37/1.62          | ~ (v2_pre_topc @ sk_B_1)
% 1.37/1.62          | (v2_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.37/1.62  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('16', plain,
% 1.37/1.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('17', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('18', plain,
% 1.37/1.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('demod', [status(thm)], ['16', '17'])).
% 1.37/1.62  thf('19', plain, ((l1_pre_topc @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('20', plain, ((v2_pre_topc @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('21', plain,
% 1.37/1.62      (![X0 : $i, X1 : $i]:
% 1.37/1.62         ((v2_struct_0 @ X0)
% 1.37/1.62          | ~ (v2_pre_topc @ X0)
% 1.37/1.62          | ~ (l1_pre_topc @ X0)
% 1.37/1.62          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.37/1.62          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X1)))
% 1.37/1.62          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.37/1.62          | ~ (m1_pre_topc @ X1 @ X0)
% 1.37/1.62          | (v2_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 1.37/1.62  thf('22', plain,
% 1.37/1.62      (![X0 : $i]:
% 1.37/1.62         ((v2_struct_0 @ sk_B_1)
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X0)))
% 1.37/1.62          | ~ (l1_pre_topc @ sk_D)
% 1.37/1.62          | ~ (v2_pre_topc @ sk_D)
% 1.37/1.62          | (v2_struct_0 @ sk_D))),
% 1.37/1.62      inference('sup-', [status(thm)], ['9', '21'])).
% 1.37/1.62  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('24', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('25', plain, ((l1_pre_topc @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['23', '24'])).
% 1.37/1.62  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('27', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['26', '27'])).
% 1.37/1.62  thf('29', plain,
% 1.37/1.62      (![X0 : $i]:
% 1.37/1.62         ((v2_struct_0 @ sk_B_1)
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X0)))
% 1.37/1.62          | (v2_struct_0 @ sk_D))),
% 1.37/1.62      inference('demod', [status(thm)], ['22', '25', '28'])).
% 1.37/1.62  thf('30', plain,
% 1.37/1.62      (![X0 : $i]:
% 1.37/1.62         ((v2_struct_0 @ sk_D)
% 1.37/1.62          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X0)))
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | (v2_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.62  thf('31', plain,
% 1.37/1.62      (((v2_struct_0 @ sk_B_1)
% 1.37/1.62        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.37/1.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.37/1.62        | (v2_struct_0 @ sk_D))),
% 1.37/1.62      inference('sup-', [status(thm)], ['6', '30'])).
% 1.37/1.62  thf('32', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('33', plain,
% 1.37/1.62      (((v2_struct_0 @ sk_D)
% 1.37/1.62        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.37/1.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.37/1.62      inference('clc', [status(thm)], ['31', '32'])).
% 1.37/1.62  thf('34', plain, (~ (v2_struct_0 @ sk_D)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('35', plain,
% 1.37/1.62      (((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 1.37/1.62         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 1.37/1.62      inference('clc', [status(thm)], ['33', '34'])).
% 1.37/1.62  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['4', '5'])).
% 1.37/1.62  thf('37', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_E @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.62      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.62  thf(d4_tmap_1, axiom,
% 1.37/1.62    (![A:$i]:
% 1.37/1.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.37/1.62       ( ![B:$i]:
% 1.37/1.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.37/1.62             ( l1_pre_topc @ B ) ) =>
% 1.37/1.62           ( ![C:$i]:
% 1.37/1.62             ( ( ( v1_funct_1 @ C ) & 
% 1.37/1.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.62                 ( m1_subset_1 @
% 1.37/1.62                   C @ 
% 1.37/1.62                   ( k1_zfmisc_1 @
% 1.37/1.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.62               ( ![D:$i]:
% 1.37/1.62                 ( ( m1_pre_topc @ D @ A ) =>
% 1.37/1.62                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.37/1.62                     ( k2_partfun1 @
% 1.37/1.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.37/1.62                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.62  thf('38', plain,
% 1.37/1.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.37/1.62         ((v2_struct_0 @ X22)
% 1.37/1.62          | ~ (v2_pre_topc @ X22)
% 1.37/1.62          | ~ (l1_pre_topc @ X22)
% 1.37/1.62          | ~ (m1_pre_topc @ X23 @ X24)
% 1.37/1.62          | ((k2_tmap_1 @ X24 @ X22 @ X25 @ X23)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 1.37/1.62                 X25 @ (u1_struct_0 @ X23)))
% 1.37/1.62          | ~ (m1_subset_1 @ X25 @ 
% 1.37/1.62               (k1_zfmisc_1 @ 
% 1.37/1.62                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 1.37/1.62          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 1.37/1.62          | ~ (v1_funct_1 @ X25)
% 1.37/1.62          | ~ (l1_pre_topc @ X24)
% 1.37/1.62          | ~ (v2_pre_topc @ X24)
% 1.37/1.62          | (v2_struct_0 @ X24))),
% 1.37/1.62      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.37/1.62  thf('39', plain,
% 1.37/1.62      (![X0 : $i]:
% 1.37/1.62         ((v2_struct_0 @ sk_D)
% 1.37/1.62          | ~ (v2_pre_topc @ sk_D)
% 1.37/1.62          | ~ (l1_pre_topc @ sk_D)
% 1.37/1.62          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.37/1.62               (u1_struct_0 @ sk_B_1))
% 1.37/1.62          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X0)))
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | ~ (l1_pre_topc @ sk_B_1)
% 1.37/1.62          | ~ (v2_pre_topc @ sk_B_1)
% 1.37/1.62          | (v2_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('sup-', [status(thm)], ['37', '38'])).
% 1.37/1.62  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['26', '27'])).
% 1.37/1.62  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 1.37/1.62      inference('demod', [status(thm)], ['23', '24'])).
% 1.37/1.62  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('43', plain,
% 1.37/1.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('demod', [status(thm)], ['16', '17'])).
% 1.37/1.62  thf('44', plain, ((l1_pre_topc @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('45', plain, ((v2_pre_topc @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('46', plain,
% 1.37/1.62      (![X0 : $i]:
% 1.37/1.62         ((v2_struct_0 @ sk_D)
% 1.37/1.62          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 1.37/1.62              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62                 sk_E @ (u1_struct_0 @ X0)))
% 1.37/1.62          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.37/1.62          | (v2_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('demod', [status(thm)],
% 1.37/1.62                ['39', '40', '41', '42', '43', '44', '45'])).
% 1.37/1.62  thf('47', plain,
% 1.37/1.62      (((v2_struct_0 @ sk_B_1)
% 1.37/1.62        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.37/1.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               sk_E @ (u1_struct_0 @ sk_C_1)))
% 1.37/1.62        | (v2_struct_0 @ sk_D))),
% 1.37/1.62      inference('sup-', [status(thm)], ['36', '46'])).
% 1.37/1.62  thf('48', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('49', plain,
% 1.37/1.62      (((v2_struct_0 @ sk_D)
% 1.37/1.62        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.37/1.62            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 1.37/1.62      inference('clc', [status(thm)], ['47', '48'])).
% 1.37/1.62  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('51', plain,
% 1.37/1.62      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.37/1.62         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 1.37/1.62      inference('clc', [status(thm)], ['49', '50'])).
% 1.37/1.62  thf('52', plain,
% 1.37/1.62      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.37/1.62         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 1.37/1.62      inference('sup+', [status(thm)], ['35', '51'])).
% 1.37/1.62  thf('53', plain,
% 1.37/1.62      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('54', plain, (((sk_D) = (sk_A))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('55', plain,
% 1.37/1.62      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.62        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 1.37/1.62      inference('demod', [status(thm)], ['53', '54'])).
% 1.37/1.62  thf('56', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_E @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.62      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.62  thf(redefinition_r1_funct_2, axiom,
% 1.37/1.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.37/1.62     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.37/1.62         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.37/1.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.37/1.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.37/1.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.37/1.62       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.37/1.62  thf('57', plain,
% 1.37/1.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.37/1.62          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 1.37/1.62          | ~ (v1_funct_1 @ X16)
% 1.37/1.62          | (v1_xboole_0 @ X19)
% 1.37/1.62          | (v1_xboole_0 @ X18)
% 1.37/1.62          | ~ (v1_funct_1 @ X20)
% 1.37/1.62          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 1.37/1.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.37/1.62          | ((X16) = (X20))
% 1.37/1.62          | ~ (r1_funct_2 @ X17 @ X18 @ X21 @ X19 @ X16 @ X20))),
% 1.37/1.62      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.37/1.62  thf('58', plain,
% 1.37/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 1.37/1.62             X1 @ sk_E @ X0)
% 1.37/1.62          | ((sk_E) = (X0))
% 1.37/1.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.37/1.62          | ~ (v1_funct_1 @ X0)
% 1.37/1.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62          | (v1_xboole_0 @ X1)
% 1.37/1.62          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 1.37/1.62               (u1_struct_0 @ sk_B_1)))),
% 1.37/1.62      inference('sup-', [status(thm)], ['56', '57'])).
% 1.37/1.62  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('60', plain,
% 1.37/1.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('demod', [status(thm)], ['16', '17'])).
% 1.37/1.62  thf('61', plain,
% 1.37/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 1.37/1.62             X1 @ sk_E @ X0)
% 1.37/1.62          | ((sk_E) = (X0))
% 1.37/1.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.37/1.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.37/1.62          | ~ (v1_funct_1 @ X0)
% 1.37/1.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62          | (v1_xboole_0 @ X1))),
% 1.37/1.62      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.37/1.62  thf('62', plain,
% 1.37/1.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62        | ~ (v1_funct_1 @ sk_G)
% 1.37/1.62        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62        | ~ (m1_subset_1 @ sk_G @ 
% 1.37/1.62             (k1_zfmisc_1 @ 
% 1.37/1.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))
% 1.37/1.62        | ((sk_E) = (sk_G)))),
% 1.37/1.62      inference('sup-', [status(thm)], ['55', '61'])).
% 1.37/1.62  thf('63', plain, ((v1_funct_1 @ sk_G)),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('64', plain,
% 1.37/1.62      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('65', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_G @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.62  thf('66', plain,
% 1.37/1.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.62        | ((sk_E) = (sk_G)))),
% 1.37/1.62      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 1.37/1.62  thf('67', plain,
% 1.37/1.62      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.37/1.62      inference('simplify', [status(thm)], ['66'])).
% 1.37/1.62  thf(d10_xboole_0, axiom,
% 1.37/1.62    (![A:$i,B:$i]:
% 1.37/1.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.37/1.62  thf('68', plain,
% 1.37/1.62      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.37/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.62  thf('69', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.37/1.62      inference('simplify', [status(thm)], ['68'])).
% 1.37/1.62  thf(t3_subset, axiom,
% 1.37/1.62    (![A:$i,B:$i]:
% 1.37/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.37/1.62  thf('70', plain,
% 1.37/1.62      (![X10 : $i, X12 : $i]:
% 1.37/1.62         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.37/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.62  thf('71', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.37/1.62      inference('sup-', [status(thm)], ['69', '70'])).
% 1.37/1.62  thf(cc4_relset_1, axiom,
% 1.37/1.62    (![A:$i,B:$i]:
% 1.37/1.62     ( ( v1_xboole_0 @ A ) =>
% 1.37/1.62       ( ![C:$i]:
% 1.37/1.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.37/1.62           ( v1_xboole_0 @ C ) ) ) ))).
% 1.37/1.62  thf('72', plain,
% 1.37/1.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.62         (~ (v1_xboole_0 @ X13)
% 1.37/1.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 1.37/1.62          | (v1_xboole_0 @ X14))),
% 1.37/1.62      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.37/1.62  thf('73', plain,
% 1.37/1.62      (![X0 : $i, X1 : $i]:
% 1.37/1.62         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.62      inference('sup-', [status(thm)], ['71', '72'])).
% 1.37/1.62  thf('74', plain,
% 1.37/1.62      ((m1_subset_1 @ sk_E @ 
% 1.37/1.62        (k1_zfmisc_1 @ 
% 1.37/1.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.63  thf('75', plain,
% 1.37/1.63      (![X10 : $i, X11 : $i]:
% 1.37/1.63         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.37/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.63  thf('76', plain,
% 1.37/1.63      ((r1_tarski @ sk_E @ 
% 1.37/1.63        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['74', '75'])).
% 1.37/1.63  thf(d3_tarski, axiom,
% 1.37/1.63    (![A:$i,B:$i]:
% 1.37/1.63     ( ( r1_tarski @ A @ B ) <=>
% 1.37/1.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.37/1.63  thf('77', plain,
% 1.37/1.63      (![X4 : $i, X6 : $i]:
% 1.37/1.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.37/1.63      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.63  thf(d1_xboole_0, axiom,
% 1.37/1.63    (![A:$i]:
% 1.37/1.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.37/1.63  thf('78', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.37/1.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.37/1.63  thf('79', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.63      inference('sup-', [status(thm)], ['77', '78'])).
% 1.37/1.63  thf('80', plain,
% 1.37/1.63      (![X7 : $i, X9 : $i]:
% 1.37/1.63         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.37/1.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.63  thf('81', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i]:
% 1.37/1.63         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['79', '80'])).
% 1.37/1.63  thf('82', plain,
% 1.37/1.63      ((((sk_E) = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1)))
% 1.37/1.63        | ~ (v1_xboole_0 @ 
% 1.37/1.63             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['76', '81'])).
% 1.37/1.63  thf('83', plain,
% 1.37/1.63      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.63        | ((sk_E)
% 1.37/1.63            = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['73', '82'])).
% 1.37/1.63  thf('84', plain,
% 1.37/1.63      ((((sk_E) = (sk_G))
% 1.37/1.63        | ((sk_E)
% 1.37/1.63            = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['67', '83'])).
% 1.37/1.63  thf('85', plain,
% 1.37/1.63      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.37/1.63      inference('simplify', [status(thm)], ['66'])).
% 1.37/1.63  thf('86', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i]:
% 1.37/1.63         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.63      inference('sup-', [status(thm)], ['71', '72'])).
% 1.37/1.63  thf('87', plain,
% 1.37/1.63      ((m1_subset_1 @ sk_G @ 
% 1.37/1.63        (k1_zfmisc_1 @ 
% 1.37/1.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('88', plain,
% 1.37/1.63      (![X10 : $i, X11 : $i]:
% 1.37/1.63         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.37/1.63      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.63  thf('89', plain,
% 1.37/1.63      ((r1_tarski @ sk_G @ 
% 1.37/1.63        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['87', '88'])).
% 1.37/1.63  thf('90', plain,
% 1.37/1.63      (![X0 : $i, X1 : $i]:
% 1.37/1.63         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['79', '80'])).
% 1.37/1.63  thf('91', plain,
% 1.37/1.63      ((((sk_G) = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1)))
% 1.37/1.63        | ~ (v1_xboole_0 @ 
% 1.37/1.63             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['89', '90'])).
% 1.37/1.63  thf('92', plain,
% 1.37/1.63      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.37/1.63        | ((sk_G)
% 1.37/1.63            = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['86', '91'])).
% 1.37/1.63  thf('93', plain,
% 1.37/1.63      ((((sk_E) = (sk_G))
% 1.37/1.63        | ((sk_G)
% 1.37/1.63            = (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 1.37/1.63      inference('sup-', [status(thm)], ['85', '92'])).
% 1.37/1.63  thf('94', plain,
% 1.37/1.63      ((((sk_G) = (sk_E)) | ((sk_E) = (sk_G)) | ((sk_E) = (sk_G)))),
% 1.37/1.63      inference('sup+', [status(thm)], ['84', '93'])).
% 1.37/1.63  thf('95', plain, (((sk_G) = (sk_E))),
% 1.37/1.63      inference('simplify', [status(thm)], ['94'])).
% 1.37/1.63  thf('96', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 1.37/1.63        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('97', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('split', [status(esa)], ['96'])).
% 1.37/1.63  thf('98', plain, (((sk_D) = (sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('99', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('demod', [status(thm)], ['97', '98'])).
% 1.37/1.63  thf('100', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('sup+', [status(thm)], ['95', '99'])).
% 1.37/1.63  thf('101', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('sup+', [status(thm)], ['52', '100'])).
% 1.37/1.63  thf('102', plain,
% 1.37/1.63      (~
% 1.37/1.63       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) | 
% 1.37/1.63       ~
% 1.37/1.63       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.37/1.63      inference('split', [status(esa)], ['0'])).
% 1.37/1.63  thf('103', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.37/1.63      inference('split', [status(esa)], ['96'])).
% 1.37/1.63  thf('104', plain, (((sk_D) = (sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('105', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.63         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.37/1.63      inference('demod', [status(thm)], ['103', '104'])).
% 1.37/1.63  thf('106', plain,
% 1.37/1.63      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 1.37/1.63         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 1.37/1.63      inference('sup+', [status(thm)], ['35', '51'])).
% 1.37/1.63  thf('107', plain, (((sk_G) = (sk_E))),
% 1.37/1.63      inference('simplify', [status(thm)], ['94'])).
% 1.37/1.63  thf('108', plain,
% 1.37/1.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.37/1.63         <= (~
% 1.37/1.63             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('split', [status(esa)], ['0'])).
% 1.37/1.63  thf('109', plain, (((sk_D) = (sk_A))),
% 1.37/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.63  thf('110', plain,
% 1.37/1.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 1.37/1.63         <= (~
% 1.37/1.63             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('demod', [status(thm)], ['108', '109'])).
% 1.37/1.63  thf('111', plain,
% 1.37/1.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 1.37/1.63         <= (~
% 1.37/1.63             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['107', '110'])).
% 1.37/1.63  thf('112', plain,
% 1.37/1.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 1.37/1.63         <= (~
% 1.37/1.63             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.37/1.63      inference('sup-', [status(thm)], ['106', '111'])).
% 1.37/1.63  thf('113', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 1.37/1.63       ~
% 1.37/1.63       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 1.37/1.63      inference('sup-', [status(thm)], ['105', '112'])).
% 1.37/1.63  thf('114', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 1.37/1.63       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 1.37/1.63      inference('split', [status(esa)], ['96'])).
% 1.37/1.63  thf('115', plain,
% 1.37/1.63      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 1.37/1.63      inference('sat_resolution*', [status(thm)], ['102', '113', '114'])).
% 1.37/1.63  thf('116', plain,
% 1.37/1.63      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63        (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)),
% 1.37/1.63      inference('simpl_trail', [status(thm)], ['101', '115'])).
% 1.37/1.63  thf('117', plain,
% 1.37/1.63      (($false)
% 1.37/1.63         <= (~
% 1.37/1.63             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 1.37/1.63      inference('demod', [status(thm)], ['3', '116'])).
% 1.37/1.63  thf('118', plain,
% 1.37/1.63      (~
% 1.37/1.63       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.37/1.63         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 1.37/1.63      inference('sat_resolution*', [status(thm)], ['102', '113'])).
% 1.37/1.63  thf('119', plain, ($false),
% 1.37/1.63      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 1.37/1.63  
% 1.37/1.63  % SZS output end Refutation
% 1.37/1.63  
% 1.47/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
