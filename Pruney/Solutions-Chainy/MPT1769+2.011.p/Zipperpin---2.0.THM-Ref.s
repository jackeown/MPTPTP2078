%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NavSYO4IHh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:11 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  144 (1082 expanded)
%              Number of leaves         :   29 ( 305 expanded)
%              Depth                    :   19
%              Number of atoms          : 1721 (59278 expanded)
%              Number of equality atoms :   65 ( 786 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( X5 = X9 )
      | ~ ( r1_funct_2 @ X6 @ X7 @ X10 @ X8 @ X5 @ X9 ) ) ),
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

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('73',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( sk_F = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_E = sk_G )
    | ( sk_F = sk_E )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_F = sk_E )
    | ( sk_E = sk_G ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('82',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( sk_F = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('87',plain,
    ( ( sk_E = sk_G )
    | ( sk_F = sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_F = sk_G )
    | ( sk_E = sk_G ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( sk_E = sk_G )
    | ( sk_E = sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['80','88'])).

thf('90',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['52','95'])).

thf('97',plain,
    ( $false
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['3','96'])).

thf('98',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('99',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('100',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['89'])).

thf('101',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('107',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['98','109'])).

thf('111',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['98','109','111'])).

thf('113',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['97','110','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NavSYO4IHh
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 686 iterations in 0.427s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.69/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.89  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.89  thf(sk_F_type, type, sk_F: $i).
% 0.69/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.89  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(sk_G_type, type, sk_G: $i).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.89  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.69/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.89  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.69/0.89  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.89  thf(t80_tmap_1, conjecture,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.89             ( l1_pre_topc @ B ) ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.89               ( ![D:$i]:
% 0.69/0.89                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.69/0.89                   ( ![E:$i]:
% 0.69/0.89                     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.89                         ( v1_funct_2 @
% 0.69/0.89                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                         ( m1_subset_1 @
% 0.69/0.89                           E @ 
% 0.69/0.89                           ( k1_zfmisc_1 @
% 0.69/0.89                             ( k2_zfmisc_1 @
% 0.69/0.89                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                       ( ![F:$i]:
% 0.69/0.89                         ( ( ( v1_funct_1 @ F ) & 
% 0.69/0.89                             ( v1_funct_2 @
% 0.69/0.89                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                             ( m1_subset_1 @
% 0.69/0.89                               F @ 
% 0.69/0.89                               ( k1_zfmisc_1 @
% 0.69/0.89                                 ( k2_zfmisc_1 @
% 0.69/0.89                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                           ( ![G:$i]:
% 0.69/0.89                             ( ( ( v1_funct_1 @ G ) & 
% 0.69/0.89                                 ( v1_funct_2 @
% 0.69/0.89                                   G @ ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                   ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                                 ( m1_subset_1 @
% 0.69/0.89                                   G @ 
% 0.69/0.89                                   ( k1_zfmisc_1 @
% 0.69/0.89                                     ( k2_zfmisc_1 @
% 0.69/0.89                                       ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                               ( ( ( ( D ) = ( A ) ) & 
% 0.69/0.89                                   ( r1_funct_2 @
% 0.69/0.89                                     ( u1_struct_0 @ A ) @ 
% 0.69/0.89                                     ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                     ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.69/0.89                                 ( ( r2_funct_2 @
% 0.69/0.89                                     ( u1_struct_0 @ C ) @ 
% 0.69/0.89                                     ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.69/0.89                                   ( r2_funct_2 @
% 0.69/0.89                                     ( u1_struct_0 @ C ) @ 
% 0.69/0.89                                     ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i]:
% 0.69/0.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.89            ( l1_pre_topc @ A ) ) =>
% 0.69/0.89          ( ![B:$i]:
% 0.69/0.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.89                ( l1_pre_topc @ B ) ) =>
% 0.69/0.89              ( ![C:$i]:
% 0.69/0.89                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.89                  ( ![D:$i]:
% 0.69/0.89                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.69/0.89                      ( ![E:$i]:
% 0.69/0.89                        ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.89                            ( v1_funct_2 @
% 0.69/0.89                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                            ( m1_subset_1 @
% 0.69/0.89                              E @ 
% 0.69/0.89                              ( k1_zfmisc_1 @
% 0.69/0.89                                ( k2_zfmisc_1 @
% 0.69/0.89                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                          ( ![F:$i]:
% 0.69/0.89                            ( ( ( v1_funct_1 @ F ) & 
% 0.69/0.89                                ( v1_funct_2 @
% 0.69/0.89                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                                ( m1_subset_1 @
% 0.69/0.89                                  F @ 
% 0.69/0.89                                  ( k1_zfmisc_1 @
% 0.69/0.89                                    ( k2_zfmisc_1 @
% 0.69/0.89                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                              ( ![G:$i]:
% 0.69/0.89                                ( ( ( v1_funct_1 @ G ) & 
% 0.69/0.89                                    ( v1_funct_2 @
% 0.69/0.89                                      G @ ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                      ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                                    ( m1_subset_1 @
% 0.69/0.89                                      G @ 
% 0.69/0.89                                      ( k1_zfmisc_1 @
% 0.69/0.89                                        ( k2_zfmisc_1 @
% 0.69/0.89                                          ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                                  ( ( ( ( D ) = ( A ) ) & 
% 0.69/0.89                                      ( r1_funct_2 @
% 0.69/0.89                                        ( u1_struct_0 @ A ) @ 
% 0.69/0.89                                        ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                        ( u1_struct_0 @ D ) @ 
% 0.69/0.89                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.69/0.89                                    ( ( r2_funct_2 @
% 0.69/0.89                                        ( u1_struct_0 @ C ) @ 
% 0.69/0.89                                        ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.69/0.89                                      ( r2_funct_2 @
% 0.69/0.89                                        ( u1_struct_0 @ C ) @ 
% 0.69/0.89                                        ( u1_struct_0 @ B ) @ 
% 0.69/0.89                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.69/0.89        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.89         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.69/0.89      inference('split', [status(esa)], ['0'])).
% 0.69/0.89  thf('2', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.89         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.69/0.89      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.89  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('5', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.89  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('8', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['7', '8'])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('11', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.69/0.89  thf(d5_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.89             ( l1_pre_topc @ B ) ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( m1_pre_topc @ C @ A ) =>
% 0.69/0.89               ( ![D:$i]:
% 0.69/0.89                 ( ( m1_pre_topc @ D @ A ) =>
% 0.69/0.89                   ( ![E:$i]:
% 0.69/0.89                     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.89                         ( v1_funct_2 @
% 0.69/0.89                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                         ( m1_subset_1 @
% 0.69/0.89                           E @ 
% 0.69/0.89                           ( k1_zfmisc_1 @
% 0.69/0.89                             ( k2_zfmisc_1 @
% 0.69/0.89                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89                       ( ( m1_pre_topc @ D @ C ) =>
% 0.69/0.89                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.69/0.89                           ( k2_partfun1 @
% 0.69/0.89                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.69/0.89                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X15)
% 0.69/0.89          | ~ (v2_pre_topc @ X15)
% 0.69/0.89          | ~ (l1_pre_topc @ X15)
% 0.69/0.89          | ~ (m1_pre_topc @ X16 @ X17)
% 0.69/0.89          | ~ (m1_pre_topc @ X16 @ X18)
% 0.69/0.89          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.69/0.89                 X19 @ (u1_struct_0 @ X16)))
% 0.69/0.89          | ~ (m1_subset_1 @ X19 @ 
% 0.69/0.89               (k1_zfmisc_1 @ 
% 0.69/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.69/0.89          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.69/0.89          | ~ (v1_funct_1 @ X19)
% 0.69/0.89          | ~ (m1_pre_topc @ X18 @ X17)
% 0.69/0.89          | ~ (l1_pre_topc @ X17)
% 0.69/0.89          | ~ (v2_pre_topc @ X17)
% 0.69/0.89          | (v2_struct_0 @ X17))),
% 0.69/0.89      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X0)
% 0.69/0.89          | ~ (v2_pre_topc @ X0)
% 0.69/0.89          | ~ (l1_pre_topc @ X0)
% 0.69/0.89          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.89          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X1)))
% 0.69/0.89          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.69/0.89          | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.89          | ~ (l1_pre_topc @ sk_B)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_B)
% 0.69/0.89          | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.89  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('17', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.69/0.89  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X0)
% 0.69/0.89          | ~ (v2_pre_topc @ X0)
% 0.69/0.89          | ~ (l1_pre_topc @ X0)
% 0.69/0.89          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.69/0.89          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X1)))
% 0.69/0.89          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.69/0.89          | ~ (m1_pre_topc @ X1 @ X0)
% 0.69/0.89          | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v2_struct_0 @ sk_B)
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X0)))
% 0.69/0.89          | ~ (l1_pre_topc @ sk_D)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_D)
% 0.69/0.89          | (v2_struct_0 @ sk_D))),
% 0.69/0.89      inference('sup-', [status(thm)], ['9', '21'])).
% 0.69/0.89  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('24', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('25', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.89  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('27', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v2_struct_0 @ sk_B)
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X0)))
% 0.69/0.89          | (v2_struct_0 @ sk_D))),
% 0.69/0.89      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v2_struct_0 @ sk_D)
% 0.69/0.89          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X0)))
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('simplify', [status(thm)], ['29'])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_B)
% 0.69/0.89        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.69/0.89            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               sk_E @ (u1_struct_0 @ sk_C)))
% 0.69/0.89        | (v2_struct_0 @ sk_D))),
% 0.69/0.89      inference('sup-', [status(thm)], ['6', '30'])).
% 0.69/0.89  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_D)
% 0.69/0.89        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.69/0.89            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.69/0.89      inference('clc', [status(thm)], ['31', '32'])).
% 0.69/0.89  thf('34', plain, (~ (v2_struct_0 @ sk_D)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.69/0.89         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.69/0.89            (u1_struct_0 @ sk_C)))),
% 0.69/0.89      inference('clc', [status(thm)], ['33', '34'])).
% 0.69/0.89  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.69/0.89  thf(d4_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.69/0.89             ( l1_pre_topc @ B ) ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( ( v1_funct_1 @ C ) & 
% 0.69/0.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.89                 ( m1_subset_1 @
% 0.69/0.89                   C @ 
% 0.69/0.89                   ( k1_zfmisc_1 @
% 0.69/0.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.89               ( ![D:$i]:
% 0.69/0.89                 ( ( m1_pre_topc @ D @ A ) =>
% 0.69/0.89                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.69/0.89                     ( k2_partfun1 @
% 0.69/0.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.69/0.89                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X11)
% 0.69/0.89          | ~ (v2_pre_topc @ X11)
% 0.69/0.89          | ~ (l1_pre_topc @ X11)
% 0.69/0.89          | ~ (m1_pre_topc @ X12 @ X13)
% 0.69/0.89          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.69/0.89                 X14 @ (u1_struct_0 @ X12)))
% 0.69/0.89          | ~ (m1_subset_1 @ X14 @ 
% 0.69/0.89               (k1_zfmisc_1 @ 
% 0.69/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.69/0.89          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.69/0.89          | ~ (v1_funct_1 @ X14)
% 0.69/0.89          | ~ (l1_pre_topc @ X13)
% 0.69/0.89          | ~ (v2_pre_topc @ X13)
% 0.69/0.89          | (v2_struct_0 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v2_struct_0 @ sk_D)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_D)
% 0.69/0.89          | ~ (l1_pre_topc @ sk_D)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.89          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X0)))
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | ~ (l1_pre_topc @ sk_B)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_B)
% 0.69/0.89          | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.89  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.89  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.89  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.69/0.89  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v2_struct_0 @ sk_D)
% 0.69/0.89          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.69/0.89              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89                 sk_E @ (u1_struct_0 @ X0)))
% 0.69/0.89          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.69/0.89          | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)],
% 0.69/0.89                ['39', '40', '41', '42', '43', '44', '45'])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_B)
% 0.69/0.89        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.69/0.89            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               sk_E @ (u1_struct_0 @ sk_C)))
% 0.69/0.89        | (v2_struct_0 @ sk_D))),
% 0.69/0.89      inference('sup-', [status(thm)], ['36', '46'])).
% 0.69/0.89  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_D)
% 0.69/0.89        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.69/0.89            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.69/0.89      inference('clc', [status(thm)], ['47', '48'])).
% 0.69/0.89  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.69/0.89         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.69/0.89            (u1_struct_0 @ sk_C)))),
% 0.69/0.89      inference('clc', [status(thm)], ['49', '50'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.69/0.89         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 0.69/0.89      inference('sup+', [status(thm)], ['35', '51'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('54', plain, (((sk_D) = (sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.69/0.89      inference('demod', [status(thm)], ['53', '54'])).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_E @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.69/0.89  thf(redefinition_r1_funct_2, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.89     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.89         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.69/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.89         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.69/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.89       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.69/0.89          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 0.69/0.89          | ~ (v1_funct_1 @ X5)
% 0.69/0.89          | (v1_xboole_0 @ X8)
% 0.69/0.89          | (v1_xboole_0 @ X7)
% 0.69/0.89          | ~ (v1_funct_1 @ X9)
% 0.69/0.89          | ~ (v1_funct_2 @ X9 @ X10 @ X8)
% 0.69/0.89          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.69/0.89          | ((X5) = (X9))
% 0.69/0.89          | ~ (r1_funct_2 @ X6 @ X7 @ X10 @ X8 @ X5 @ X9))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.69/0.89             X1 @ sk_E @ X0)
% 0.69/0.89          | ((sk_E) = (X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.89          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | (v1_xboole_0 @ X1)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.89          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.89  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.69/0.89             X1 @ sk_E @ X0)
% 0.69/0.89          | ((sk_E) = (X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.89          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89        | ~ (v1_funct_1 @ sk_G)
% 0.69/0.90        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_G @ 
% 0.69/0.90             (k1_zfmisc_1 @ 
% 0.69/0.90              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.69/0.90        | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['55', '61'])).
% 0.69/0.90  thf('63', plain, ((v1_funct_1 @ sk_G)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('64', plain,
% 0.69/0.90      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('65', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_G @ 
% 0.69/0.90        (k1_zfmisc_1 @ 
% 0.69/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('66', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.69/0.90        | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.69/0.90  thf('67', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.90  thf('68', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_E @ 
% 0.69/0.90        (k1_zfmisc_1 @ 
% 0.69/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.90      inference('demod', [status(thm)], ['10', '11'])).
% 0.69/0.90  thf(cc4_relset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_xboole_0 @ A ) =>
% 0.69/0.90       ( ![C:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.69/0.90           ( v1_xboole_0 @ C ) ) ) ))).
% 0.69/0.90  thf('69', plain,
% 0.69/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X2)
% 0.69/0.90          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.69/0.90          | (v1_xboole_0 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.69/0.90  thf('70', plain,
% 0.69/0.90      (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['68', '69'])).
% 0.69/0.90  thf('71', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ sk_E))),
% 0.69/0.90      inference('sup-', [status(thm)], ['67', '70'])).
% 0.69/0.90  thf('72', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.90  thf('73', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_F @ 
% 0.69/0.90        (k1_zfmisc_1 @ 
% 0.69/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('74', plain,
% 0.69/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X2)
% 0.69/0.90          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.69/0.90          | (v1_xboole_0 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.69/0.90  thf('75', plain,
% 0.69/0.90      (((v1_xboole_0 @ sk_F) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['73', '74'])).
% 0.69/0.90  thf('76', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ sk_F))),
% 0.69/0.90      inference('sup-', [status(thm)], ['72', '75'])).
% 0.69/0.90  thf(t8_boole, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.69/0.90  thf('77', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.90  thf('78', plain,
% 0.69/0.90      (![X0 : $i]: (((sk_E) = (sk_G)) | ((sk_F) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['76', '77'])).
% 0.69/0.90  thf('79', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | ((sk_F) = (sk_E)) | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['71', '78'])).
% 0.69/0.90  thf('80', plain, ((((sk_F) = (sk_E)) | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['79'])).
% 0.69/0.90  thf('81', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.90  thf('82', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_G @ 
% 0.69/0.90        (k1_zfmisc_1 @ 
% 0.69/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('83', plain,
% 0.69/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X2)
% 0.69/0.90          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.69/0.90          | (v1_xboole_0 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.69/0.90  thf('84', plain,
% 0.69/0.90      (((v1_xboole_0 @ sk_G) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['82', '83'])).
% 0.69/0.90  thf('85', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ sk_G))),
% 0.69/0.90      inference('sup-', [status(thm)], ['81', '84'])).
% 0.69/0.90  thf('86', plain,
% 0.69/0.90      (![X0 : $i]: (((sk_E) = (sk_G)) | ((sk_F) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['76', '77'])).
% 0.69/0.90  thf('87', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | ((sk_F) = (sk_G)) | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['85', '86'])).
% 0.69/0.90  thf('88', plain, ((((sk_F) = (sk_G)) | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['87'])).
% 0.69/0.90  thf('89', plain,
% 0.69/0.90      ((((sk_E) = (sk_G)) | ((sk_E) = (sk_G)) | ((sk_E) = (sk_G)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['80', '88'])).
% 0.69/0.90  thf('90', plain, (((sk_E) = (sk_G))),
% 0.69/0.90      inference('simplify', [status(thm)], ['89'])).
% 0.69/0.90  thf('91', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.69/0.90        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('92', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('split', [status(esa)], ['91'])).
% 0.69/0.90  thf('93', plain, (((sk_D) = (sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('94', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('demod', [status(thm)], ['92', '93'])).
% 0.69/0.90  thf('95', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['90', '94'])).
% 0.69/0.90  thf('96', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['52', '95'])).
% 0.69/0.90  thf('97', plain,
% 0.69/0.90      (($false)
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) & 
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['3', '96'])).
% 0.69/0.90  thf('98', plain,
% 0.69/0.90      (~
% 0.69/0.90       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 0.69/0.90       ~
% 0.69/0.90       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.69/0.90      inference('split', [status(esa)], ['91'])).
% 0.69/0.90  thf('99', plain,
% 0.69/0.90      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.69/0.90         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 0.69/0.90      inference('sup+', [status(thm)], ['35', '51'])).
% 0.69/0.90  thf('100', plain, (((sk_E) = (sk_G))),
% 0.69/0.90      inference('simplify', [status(thm)], ['89'])).
% 0.69/0.90  thf('101', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.69/0.90         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('split', [status(esa)], ['0'])).
% 0.69/0.90  thf('102', plain, (((sk_D) = (sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('103', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.69/0.90         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('demod', [status(thm)], ['101', '102'])).
% 0.69/0.90  thf('104', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.69/0.90         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['100', '103'])).
% 0.69/0.90  thf('105', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.90         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['99', '104'])).
% 0.69/0.90  thf('106', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.69/0.90      inference('split', [status(esa)], ['91'])).
% 0.69/0.90  thf('107', plain, (((sk_D) = (sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('108', plain,
% 0.69/0.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.69/0.90      inference('demod', [status(thm)], ['106', '107'])).
% 0.69/0.90  thf('109', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.69/0.90       ~
% 0.69/0.90       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.69/0.90      inference('sup-', [status(thm)], ['105', '108'])).
% 0.69/0.90  thf('110', plain,
% 0.69/0.90      (~
% 0.69/0.90       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.69/0.90      inference('sat_resolution*', [status(thm)], ['98', '109'])).
% 0.69/0.90  thf('111', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.69/0.90       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.69/0.90      inference('split', [status(esa)], ['0'])).
% 0.69/0.90  thf('112', plain,
% 0.69/0.90      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.90         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.69/0.90      inference('sat_resolution*', [status(thm)], ['98', '109', '111'])).
% 0.69/0.90  thf('113', plain, ($false),
% 0.69/0.90      inference('simpl_trail', [status(thm)], ['97', '110', '112'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
