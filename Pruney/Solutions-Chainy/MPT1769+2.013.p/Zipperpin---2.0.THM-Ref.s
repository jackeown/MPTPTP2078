%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.12jhedF0Zo

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 819 expanded)
%              Number of leaves         :   34 ( 239 expanded)
%              Depth                    :   20
%              Number of atoms          : 1727 (43494 expanded)
%              Number of equality atoms :   53 ( 552 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X25 )
      | ( ( k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) @ X26 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( k2_tmap_1 @ X20 @ X18 @ X21 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) @ X21 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( X12 = X16 )
      | ~ ( r1_funct_2 @ X13 @ X14 @ X17 @ X15 @ X12 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('70',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_G @ X0 )
      | ( sk_E = sk_G ) ) ),
    inference('sup-',[status(thm)],['53','74'])).

thf('76',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ( sk_E = sk_G ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r1_tarski @ X0 @ sk_E )
      | ( X0 = sk_E ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_E = sk_G )
    | ( sk_G = sk_E )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['88','92'])).

thf('94',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['52','93'])).

thf('95',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['89'])).

thf('97',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('100',plain,(
    sk_E = sk_G ),
    inference(simplify,[status(thm)],['87'])).

thf('101',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['98','105'])).

thf('107',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['89'])).

thf('108',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['95','106','107'])).

thf('109',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['94','108'])).

thf('110',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','109'])).

thf('111',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['95','106'])).

thf('112',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.12jhedF0Zo
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 97 iterations in 0.045s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.19/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(t80_tmap_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                         ( v1_funct_2 @
% 0.19/0.50                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ 
% 0.19/0.50                           ( k1_zfmisc_1 @
% 0.19/0.50                             ( k2_zfmisc_1 @
% 0.19/0.50                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                       ( ![F:$i]:
% 0.19/0.50                         ( ( ( v1_funct_1 @ F ) & 
% 0.19/0.50                             ( v1_funct_2 @
% 0.19/0.50                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                             ( m1_subset_1 @
% 0.19/0.50                               F @ 
% 0.19/0.50                               ( k1_zfmisc_1 @
% 0.19/0.50                                 ( k2_zfmisc_1 @
% 0.19/0.50                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                           ( ![G:$i]:
% 0.19/0.50                             ( ( ( v1_funct_1 @ G ) & 
% 0.19/0.50                                 ( v1_funct_2 @
% 0.19/0.50                                   G @ ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                   ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                                 ( m1_subset_1 @
% 0.19/0.50                                   G @ 
% 0.19/0.50                                   ( k1_zfmisc_1 @
% 0.19/0.50                                     ( k2_zfmisc_1 @
% 0.19/0.50                                       ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                               ( ( ( ( D ) = ( A ) ) & 
% 0.19/0.50                                   ( r1_funct_2 @
% 0.19/0.50                                     ( u1_struct_0 @ A ) @ 
% 0.19/0.50                                     ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                     ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.19/0.50                                 ( ( r2_funct_2 @
% 0.19/0.50                                     ( u1_struct_0 @ C ) @ 
% 0.19/0.50                                     ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.19/0.50                                   ( r2_funct_2 @
% 0.19/0.50                                     ( u1_struct_0 @ C ) @ 
% 0.19/0.50                                     ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50                ( l1_pre_topc @ B ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50                  ( ![D:$i]:
% 0.19/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                      ( ![E:$i]:
% 0.19/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                            ( v1_funct_2 @
% 0.19/0.50                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                            ( m1_subset_1 @
% 0.19/0.50                              E @ 
% 0.19/0.50                              ( k1_zfmisc_1 @
% 0.19/0.50                                ( k2_zfmisc_1 @
% 0.19/0.50                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                          ( ![F:$i]:
% 0.19/0.50                            ( ( ( v1_funct_1 @ F ) & 
% 0.19/0.50                                ( v1_funct_2 @
% 0.19/0.50                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                                ( m1_subset_1 @
% 0.19/0.50                                  F @ 
% 0.19/0.50                                  ( k1_zfmisc_1 @
% 0.19/0.50                                    ( k2_zfmisc_1 @
% 0.19/0.50                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                              ( ![G:$i]:
% 0.19/0.50                                ( ( ( v1_funct_1 @ G ) & 
% 0.19/0.50                                    ( v1_funct_2 @
% 0.19/0.50                                      G @ ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                      ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                                    ( m1_subset_1 @
% 0.19/0.50                                      G @ 
% 0.19/0.50                                      ( k1_zfmisc_1 @
% 0.19/0.50                                        ( k2_zfmisc_1 @
% 0.19/0.50                                          ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                                  ( ( ( ( D ) = ( A ) ) & 
% 0.19/0.50                                      ( r1_funct_2 @
% 0.19/0.50                                        ( u1_struct_0 @ A ) @ 
% 0.19/0.50                                        ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                        ( u1_struct_0 @ D ) @ 
% 0.19/0.50                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.19/0.50                                    ( ( r2_funct_2 @
% 0.19/0.50                                        ( u1_struct_0 @ C ) @ 
% 0.19/0.50                                        ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.19/0.50                                      ( r2_funct_2 @
% 0.19/0.50                                        ( u1_struct_0 @ C ) @ 
% 0.19/0.50                                        ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 0.19/0.50        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('2', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('8', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('11', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf(d5_tmap_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                         ( v1_funct_2 @
% 0.19/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ 
% 0.19/0.50                           ( k1_zfmisc_1 @
% 0.19/0.50                             ( k2_zfmisc_1 @
% 0.19/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.50                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.50                           ( k2_partfun1 @
% 0.19/0.50                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.50                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X22)
% 0.19/0.50          | ~ (v2_pre_topc @ X22)
% 0.19/0.50          | ~ (l1_pre_topc @ X22)
% 0.19/0.50          | ~ (m1_pre_topc @ X23 @ X24)
% 0.19/0.50          | ~ (m1_pre_topc @ X23 @ X25)
% 0.19/0.50          | ((k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 0.19/0.50                 X26 @ (u1_struct_0 @ X23)))
% 0.19/0.50          | ~ (m1_subset_1 @ X26 @ 
% 0.19/0.50               (k1_zfmisc_1 @ 
% 0.19/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))))
% 0.19/0.50          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))
% 0.19/0.50          | ~ (v1_funct_1 @ X26)
% 0.19/0.50          | ~ (m1_pre_topc @ X25 @ X24)
% 0.19/0.50          | ~ (l1_pre_topc @ X24)
% 0.19/0.50          | ~ (v2_pre_topc @ X24)
% 0.19/0.50          | (v2_struct_0 @ X24))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('17', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X0)
% 0.19/0.50          | ~ (v2_pre_topc @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ X0)
% 0.19/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.50          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.50          | (v2_struct_0 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '21'])).
% 0.19/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | (v2_struct_0 @ sk_D))),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_D)
% 0.19/0.50          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_B)
% 0.19/0.50        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.50        | (v2_struct_0 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '30'])).
% 0.19/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_D)
% 0.19/0.50        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.19/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50            (u1_struct_0 @ sk_C_1)))),
% 0.19/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf(d4_tmap_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                 ( m1_subset_1 @
% 0.19/0.50                   C @ 
% 0.19/0.50                   ( k1_zfmisc_1 @
% 0.19/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k2_partfun1 @
% 0.19/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X18)
% 0.19/0.50          | ~ (v2_pre_topc @ X18)
% 0.19/0.50          | ~ (l1_pre_topc @ X18)
% 0.19/0.50          | ~ (m1_pre_topc @ X19 @ X20)
% 0.19/0.50          | ((k2_tmap_1 @ X20 @ X18 @ X21 @ X19)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18) @ 
% 0.19/0.50                 X21 @ (u1_struct_0 @ X19)))
% 0.19/0.50          | ~ (m1_subset_1 @ X21 @ 
% 0.19/0.50               (k1_zfmisc_1 @ 
% 0.19/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 0.19/0.50          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 0.19/0.50          | ~ (v1_funct_1 @ X21)
% 0.19/0.50          | ~ (l1_pre_topc @ X20)
% 0.19/0.50          | ~ (v2_pre_topc @ X20)
% 0.19/0.50          | (v2_struct_0 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_D)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.50  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_D)
% 0.19/0.50          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.50          | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)],
% 0.19/0.50                ['39', '40', '41', '42', '43', '44', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_B)
% 0.19/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.50        | (v2_struct_0 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['36', '46'])).
% 0.19/0.50  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_D)
% 0.19/0.50        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.19/0.50      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 0.19/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.50            (u1_struct_0 @ sk_C_1)))),
% 0.19/0.50      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 0.19/0.50         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '51'])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('55', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.19/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf(redefinition_r1_funct_2, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.50     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.50         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.19/0.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.50         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.19/0.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.50       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.19/0.50          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.19/0.50          | ~ (v1_funct_1 @ X12)
% 0.19/0.50          | (v1_xboole_0 @ X15)
% 0.19/0.50          | (v1_xboole_0 @ X14)
% 0.19/0.50          | ~ (v1_funct_1 @ X16)
% 0.19/0.50          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.19/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.19/0.50          | ((X12) = (X16))
% 0.19/0.50          | ~ (r1_funct_2 @ X13 @ X14 @ X17 @ X15 @ X12 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.19/0.50             X1 @ sk_E @ X0)
% 0.19/0.50          | ((sk_E) = (X0))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.50          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X0)
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | (v1_xboole_0 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.50  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.19/0.50             X1 @ sk_E @ X0)
% 0.19/0.50          | ((sk_E) = (X0))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.50          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X0)
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_G)
% 0.19/0.50        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ~ (m1_subset_1 @ sk_G @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | ((sk_E) = (sk_G)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['56', '62'])).
% 0.19/0.50  thf('64', plain, ((v1_funct_1 @ sk_G)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_G @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((sk_E) = (sk_G)))),
% 0.19/0.50      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.19/0.50  thf('68', plain,
% 0.19/0.50      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.19/0.50  thf(fc3_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.19/0.50  thf('70', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_G @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t5_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.50  thf('71', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X9 @ X10)
% 0.19/0.50          | ~ (v1_xboole_0 @ X11)
% 0.19/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ 
% 0.19/0.50             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_G))),
% 0.19/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.19/0.50      inference('sup-', [status(thm)], ['69', '72'])).
% 0.19/0.50  thf('74', plain,
% 0.19/0.50      (![X0 : $i]: (((sk_E) = (sk_G)) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.19/0.50      inference('sup-', [status(thm)], ['68', '73'])).
% 0.19/0.50  thf('75', plain, (![X0 : $i]: ((r1_tarski @ sk_G @ X0) | ((sk_E) = (sk_G)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['53', '74'])).
% 0.19/0.50  thf('76', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('77', plain,
% 0.19/0.50      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.19/0.50  thf('78', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.19/0.50  thf('79', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('80', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X9 @ X10)
% 0.19/0.50          | ~ (v1_xboole_0 @ X11)
% 0.19/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.50  thf('81', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ 
% 0.19/0.50             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.50  thf('82', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['78', '81'])).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      (![X0 : $i]: (((sk_E) = (sk_G)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['77', '82'])).
% 0.19/0.50  thf('84', plain, (![X0 : $i]: ((r1_tarski @ sk_E @ X0) | ((sk_E) = (sk_G)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['76', '83'])).
% 0.19/0.50  thf(d10_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('85', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i]:
% 0.19/0.50         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.50  thf('86', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E) = (sk_G)) | ~ (r1_tarski @ X0 @ sk_E) | ((X0) = (sk_E)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.19/0.50  thf('87', plain,
% 0.19/0.50      ((((sk_E) = (sk_G)) | ((sk_G) = (sk_E)) | ((sk_E) = (sk_G)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['75', '86'])).
% 0.19/0.50  thf('88', plain, (((sk_E) = (sk_G))),
% 0.19/0.50      inference('simplify', [status(thm)], ['87'])).
% 0.19/0.50  thf('89', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 0.19/0.50        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('90', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('split', [status(esa)], ['89'])).
% 0.19/0.50  thf('91', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('92', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.19/0.50  thf('93', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['88', '92'])).
% 0.19/0.50  thf('94', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['52', '93'])).
% 0.19/0.50  thf('95', plain,
% 0.19/0.50      (~
% 0.19/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)) | 
% 0.19/0.50       ~
% 0.19/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('96', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 0.19/0.50      inference('split', [status(esa)], ['89'])).
% 0.19/0.50  thf('97', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('98', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['96', '97'])).
% 0.19/0.50  thf('99', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 0.19/0.50         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '51'])).
% 0.19/0.50  thf('100', plain, (((sk_E) = (sk_G))),
% 0.19/0.50      inference('simplify', [status(thm)], ['87'])).
% 0.19/0.50  thf('101', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('102', plain, (((sk_D) = (sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('103', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['101', '102'])).
% 0.19/0.50  thf('104', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['100', '103'])).
% 0.19/0.50  thf('105', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['99', '104'])).
% 0.19/0.50  thf('106', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.19/0.50       ~
% 0.19/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 0.19/0.50      inference('sup-', [status(thm)], ['98', '105'])).
% 0.19/0.50  thf('107', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.19/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 0.19/0.50      inference('split', [status(esa)], ['89'])).
% 0.19/0.50  thf('108', plain,
% 0.19/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['95', '106', '107'])).
% 0.19/0.50  thf('109', plain,
% 0.19/0.50      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50        (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['94', '108'])).
% 0.19/0.50  thf('110', plain,
% 0.19/0.50      (($false)
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '109'])).
% 0.19/0.50  thf('111', plain,
% 0.19/0.50      (~
% 0.19/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['95', '106'])).
% 0.19/0.50  thf('112', plain, ($false),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
