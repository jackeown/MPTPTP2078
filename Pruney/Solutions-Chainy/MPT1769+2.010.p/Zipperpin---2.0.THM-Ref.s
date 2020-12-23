%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acE8y8AJDk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 933 expanded)
%              Number of leaves         :   35 ( 269 expanded)
%              Depth                    :   20
%              Number of atoms          : 1894 (48123 expanded)
%              Number of equality atoms :   52 ( 600 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X28 )
      | ( ( k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ X29 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
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
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
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
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k2_tmap_1 @ X23 @ X21 @ X24 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) @ X24 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_D @ sk_E @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_G @ sk_E )
    | ( r2_hidden @ ( sk_D @ sk_E @ sk_G @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) @ sk_G ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( X15 = X19 )
      | ~ ( r1_funct_2 @ X16 @ X17 @ X20 @ X18 @ X15 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('77',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_G @ sk_E )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['57','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('86',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_D @ sk_G @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_tarski @ sk_E @ sk_G )
    | ( r2_hidden @ ( sk_D @ sk_G @ sk_E @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) @ sk_E ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('93',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,
    ( ( r1_tarski @ sk_E @ sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ( sk_E = sk_G )
    | ~ ( r1_tarski @ sk_G @ sk_E )
    | ( sk_G = sk_E ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ sk_G @ sk_E )
    | ( sk_E = sk_G ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['84','100'])).

thf('102',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['101','105'])).

thf('107',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['52','106'])).

thf('108',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['102'])).

thf('110',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('113',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['84','100'])).

thf('114',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,(
    sk_D_1 = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['102'])).

thf('121',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['108','119','120'])).

thf('122',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['107','121'])).

thf('123',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','122'])).

thf('124',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['108','119'])).

thf('125',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.acE8y8AJDk
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 157 iterations in 0.064s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.22/0.55  thf(t80_tmap_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55             ( l1_pre_topc @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.55                   ( ![E:$i]:
% 0.22/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.55                         ( v1_funct_2 @
% 0.22/0.55                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                         ( m1_subset_1 @
% 0.22/0.55                           E @ 
% 0.22/0.55                           ( k1_zfmisc_1 @
% 0.22/0.55                             ( k2_zfmisc_1 @
% 0.22/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                       ( ![F:$i]:
% 0.22/0.55                         ( ( ( v1_funct_1 @ F ) & 
% 0.22/0.55                             ( v1_funct_2 @
% 0.22/0.55                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                             ( m1_subset_1 @
% 0.22/0.55                               F @ 
% 0.22/0.55                               ( k1_zfmisc_1 @
% 0.22/0.55                                 ( k2_zfmisc_1 @
% 0.22/0.55                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                           ( ![G:$i]:
% 0.22/0.55                             ( ( ( v1_funct_1 @ G ) & 
% 0.22/0.55                                 ( v1_funct_2 @
% 0.22/0.55                                   G @ ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                   ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                                 ( m1_subset_1 @
% 0.22/0.55                                   G @ 
% 0.22/0.55                                   ( k1_zfmisc_1 @
% 0.22/0.55                                     ( k2_zfmisc_1 @
% 0.22/0.55                                       ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                               ( ( ( ( D ) = ( A ) ) & 
% 0.22/0.55                                   ( r1_funct_2 @
% 0.22/0.55                                     ( u1_struct_0 @ A ) @ 
% 0.22/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                     ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.22/0.55                                 ( ( r2_funct_2 @
% 0.22/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.22/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.22/0.55                                   ( r2_funct_2 @
% 0.22/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.22/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55            ( l1_pre_topc @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55                ( l1_pre_topc @ B ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.55                  ( ![D:$i]:
% 0.22/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.55                      ( ![E:$i]:
% 0.22/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.55                            ( v1_funct_2 @
% 0.22/0.55                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                            ( m1_subset_1 @
% 0.22/0.55                              E @ 
% 0.22/0.55                              ( k1_zfmisc_1 @
% 0.22/0.55                                ( k2_zfmisc_1 @
% 0.22/0.55                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                          ( ![F:$i]:
% 0.22/0.55                            ( ( ( v1_funct_1 @ F ) & 
% 0.22/0.55                                ( v1_funct_2 @
% 0.22/0.55                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                                ( m1_subset_1 @
% 0.22/0.55                                  F @ 
% 0.22/0.55                                  ( k1_zfmisc_1 @
% 0.22/0.55                                    ( k2_zfmisc_1 @
% 0.22/0.55                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                              ( ![G:$i]:
% 0.22/0.55                                ( ( ( v1_funct_1 @ G ) & 
% 0.22/0.55                                    ( v1_funct_2 @
% 0.22/0.55                                      G @ ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                      ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                                    ( m1_subset_1 @
% 0.22/0.55                                      G @ 
% 0.22/0.55                                      ( k1_zfmisc_1 @
% 0.22/0.55                                        ( k2_zfmisc_1 @
% 0.22/0.55                                          ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                                  ( ( ( ( D ) = ( A ) ) & 
% 0.22/0.55                                      ( r1_funct_2 @
% 0.22/0.55                                        ( u1_struct_0 @ A ) @ 
% 0.22/0.55                                        ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                        ( u1_struct_0 @ D ) @ 
% 0.22/0.55                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.22/0.55                                    ( ( r2_funct_2 @
% 0.22/0.55                                        ( u1_struct_0 @ C ) @ 
% 0.22/0.55                                        ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.22/0.55                                      ( r2_funct_2 @
% 0.22/0.55                                        ( u1_struct_0 @ C ) @ 
% 0.22/0.55                                        ( u1_struct_0 @ B ) @ 
% 0.22/0.55                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.22/0.55        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55             (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55           (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('5', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('9', plain, ((m1_pre_topc @ sk_D_1 @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('11', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(d5_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55             ( l1_pre_topc @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.55                   ( ![E:$i]:
% 0.22/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.55                         ( v1_funct_2 @
% 0.22/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                         ( m1_subset_1 @
% 0.22/0.55                           E @ 
% 0.22/0.55                           ( k1_zfmisc_1 @
% 0.22/0.55                             ( k2_zfmisc_1 @
% 0.22/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                       ( ( m1_pre_topc @ D @ C ) =>
% 0.22/0.55                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.55                           ( k2_partfun1 @
% 0.22/0.55                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.22/0.55                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X25)
% 0.22/0.55          | ~ (v2_pre_topc @ X25)
% 0.22/0.55          | ~ (l1_pre_topc @ X25)
% 0.22/0.55          | ~ (m1_pre_topc @ X26 @ X27)
% 0.22/0.55          | ~ (m1_pre_topc @ X26 @ X28)
% 0.22/0.55          | ((k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 0.22/0.55                 X29 @ (u1_struct_0 @ X26)))
% 0.22/0.55          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 0.22/0.55          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 0.22/0.55          | ~ (v1_funct_1 @ X29)
% 0.22/0.55          | ~ (m1_pre_topc @ X28 @ X27)
% 0.22/0.55          | ~ (l1_pre_topc @ X27)
% 0.22/0.55          | ~ (v2_pre_topc @ X27)
% 0.22/0.55          | (v2_struct_0 @ X27))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.22/0.55               (u1_struct_0 @ sk_B))
% 0.22/0.55          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.55          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.22/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('17', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.22/0.55          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.55          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.22/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | ((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (l1_pre_topc @ sk_D_1)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_D_1)
% 0.22/0.55          | (v2_struct_0 @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '21'])).
% 0.22/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('24', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('28', plain, ((v2_pre_topc @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | ((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.55          | (v2_struct_0 @ sk_D_1))),
% 0.22/0.55      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_D_1)
% 0.22/0.55          | ((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ X0 @ sk_E)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '30'])).
% 0.22/0.55  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_D_1)
% 0.22/0.55        | ((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.22/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.55  thf('34', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (((k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E)
% 0.22/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.22/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.55  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(d4_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55             ( l1_pre_topc @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                 ( m1_subset_1 @
% 0.22/0.55                   C @ 
% 0.22/0.55                   ( k1_zfmisc_1 @
% 0.22/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.55                     ( k2_partfun1 @
% 0.22/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X21)
% 0.22/0.55          | ~ (v2_pre_topc @ X21)
% 0.22/0.55          | ~ (l1_pre_topc @ X21)
% 0.22/0.55          | ~ (m1_pre_topc @ X22 @ X23)
% 0.22/0.55          | ((k2_tmap_1 @ X23 @ X21 @ X24 @ X22)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21) @ 
% 0.22/0.55                 X24 @ (u1_struct_0 @ X22)))
% 0.22/0.55          | ~ (m1_subset_1 @ X24 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))))
% 0.22/0.55          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))
% 0.22/0.55          | ~ (v1_funct_1 @ X24)
% 0.22/0.55          | ~ (l1_pre_topc @ X23)
% 0.22/0.55          | ~ (v2_pre_topc @ X23)
% 0.22/0.55          | (v2_struct_0 @ X23))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_D_1)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_D_1)
% 0.22/0.55          | ~ (l1_pre_topc @ sk_D_1)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.22/0.55               (u1_struct_0 @ sk_B))
% 0.22/0.55          | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('40', plain, ((v2_pre_topc @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('41', plain, ((l1_pre_topc @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_D_1)
% 0.22/0.55          | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X0)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)],
% 0.22/0.55                ['39', '40', '41', '42', '43', '44', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.55        | (v2_struct_0 @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['36', '46'])).
% 0.22/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_D_1)
% 0.22/0.55        | ((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.22/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.22/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      (((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.22/0.55         = (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E))),
% 0.22/0.55      inference('sup+', [status(thm)], ['35', '51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_G @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(t7_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55           ( ( ![D:$i]:
% 0.22/0.55               ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.55                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.55             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.55          | (r1_tarski @ X5 @ X3)
% 0.22/0.55          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (sk_D @ sk_E @ X0 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))) @ 
% 0.22/0.55             X0)
% 0.22/0.55          | (r1_tarski @ X0 @ sk_E))),
% 0.22/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      (((r1_tarski @ sk_G @ sk_E)
% 0.22/0.55        | (r2_hidden @ 
% 0.22/0.55           (sk_D @ sk_E @ sk_G @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))) @ 
% 0.22/0.55           sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '56'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55        (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('59', plain, (((sk_D_1) = (sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      ((r1_funct_2 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55        (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(redefinition_r1_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.22/0.55         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.55         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.22/0.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.22/0.55       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.22/0.55          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.22/0.55          | ~ (v1_funct_1 @ X15)
% 0.22/0.55          | (v1_xboole_0 @ X18)
% 0.22/0.55          | (v1_xboole_0 @ X17)
% 0.22/0.55          | ~ (v1_funct_1 @ X19)
% 0.22/0.55          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.22/0.55          | ((X15) = (X19))
% 0.22/0.55          | ~ (r1_funct_2 @ X16 @ X17 @ X20 @ X18 @ X15 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.22/0.55             X1 @ sk_E @ X0)
% 0.22/0.55          | ((sk_E) = (X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.22/0.55          | ~ (v1_funct_1 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55          | (v1_xboole_0 @ X1)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.22/0.55               (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.55  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.22/0.55             X1 @ sk_E @ X0)
% 0.22/0.55          | ((sk_E) = (X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.22/0.55          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.22/0.55          | ~ (v1_funct_1 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55          | (v1_xboole_0 @ X1))),
% 0.22/0.55      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | ~ (v1_funct_1 @ sk_G)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | ~ (m1_subset_1 @ sk_G @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))
% 0.22/0.55        | ((sk_E) = (sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['60', '66'])).
% 0.22/0.55  thf('68', plain, ((v1_funct_1 @ sk_G)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_G @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | ((sk_E) = (sk_G)))),
% 0.22/0.55      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.22/0.55  thf(t3_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      (![X6 : $i, X8 : $i]:
% 0.22/0.55         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.55  thf('76', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.55  thf(cc4_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.55           ( v1_xboole_0 @ C ) ) ) ))).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ X12)
% 0.22/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.22/0.55          | (v1_xboole_0 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_G @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t5_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.55          | ~ (v1_xboole_0 @ X11)
% 0.22/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ 
% 0.22/0.55             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['78', '81'])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (![X0 : $i]: (((sk_E) = (sk_G)) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['72', '82'])).
% 0.22/0.55  thf('84', plain, (((r1_tarski @ sk_G @ sk_E) | ((sk_E) = (sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '83'])).
% 0.22/0.55  thf('85', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_E @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('86', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_G @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.55          | (r1_tarski @ X5 @ X3)
% 0.22/0.55          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.55  thf('88', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (sk_D @ sk_G @ X0 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))) @ 
% 0.22/0.55             X0)
% 0.22/0.55          | (r1_tarski @ X0 @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      (((r1_tarski @ sk_E @ sk_G)
% 0.22/0.55        | (r2_hidden @ 
% 0.22/0.55           (sk_D @ sk_G @ sk_E @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))) @ 
% 0.22/0.55           sk_E))),
% 0.22/0.55      inference('sup-', [status(thm)], ['85', '88'])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.38/0.55  thf('91', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.38/0.55  thf('92', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf('93', plain,
% 0.38/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X9 @ X10)
% 0.38/0.55          | ~ (v1_xboole_0 @ X11)
% 0.38/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.55  thf('94', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ 
% 0.38/0.55             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.38/0.55          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.55  thf('95', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['91', '94'])).
% 0.38/0.55  thf('96', plain,
% 0.38/0.55      (![X0 : $i]: (((sk_E) = (sk_G)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['90', '95'])).
% 0.38/0.55  thf('97', plain, (((r1_tarski @ sk_E @ sk_G) | ((sk_E) = (sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['89', '96'])).
% 0.38/0.55  thf('98', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.55  thf('99', plain,
% 0.38/0.55      ((((sk_E) = (sk_G)) | ~ (r1_tarski @ sk_G @ sk_E) | ((sk_G) = (sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.38/0.55  thf('100', plain, ((~ (r1_tarski @ sk_G @ sk_E) | ((sk_E) = (sk_G)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['99'])).
% 0.38/0.55  thf('101', plain, (((sk_E) = (sk_G))),
% 0.38/0.55      inference('clc', [status(thm)], ['84', '100'])).
% 0.38/0.55  thf('102', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.38/0.55        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('103', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('split', [status(esa)], ['102'])).
% 0.38/0.55  thf('104', plain, (((sk_D_1) = (sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('105', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.38/0.55  thf('106', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['101', '105'])).
% 0.38/0.55  thf('107', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['52', '106'])).
% 0.38/0.55  thf('108', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.38/0.55       ~
% 0.38/0.55       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('109', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.38/0.55      inference('split', [status(esa)], ['102'])).
% 0.38/0.55  thf('110', plain, (((sk_D_1) = (sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('111', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.38/0.55         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['109', '110'])).
% 0.38/0.55  thf('112', plain,
% 0.38/0.55      (((k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C)
% 0.38/0.55         = (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E))),
% 0.38/0.55      inference('sup+', [status(thm)], ['35', '51'])).
% 0.38/0.55  thf('113', plain, (((sk_E) = (sk_G))),
% 0.38/0.55      inference('clc', [status(thm)], ['84', '100'])).
% 0.38/0.55  thf('114', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('115', plain, (((sk_D_1) = (sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('116', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['114', '115'])).
% 0.38/0.55  thf('117', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_D_1 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['113', '116'])).
% 0.38/0.55  thf('118', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['112', '117'])).
% 0.38/0.55  thf('119', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.38/0.55       ~
% 0.38/0.55       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.38/0.55      inference('sup-', [status(thm)], ['111', '118'])).
% 0.38/0.55  thf('120', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.38/0.55       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.38/0.55      inference('split', [status(esa)], ['102'])).
% 0.38/0.55  thf('121', plain,
% 0.38/0.55      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_G) @ sk_F))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['108', '119', '120'])).
% 0.38/0.55  thf('122', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k2_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_C) @ sk_F)),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['107', '121'])).
% 0.38/0.55  thf('123', plain,
% 0.38/0.55      (($false)
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '122'])).
% 0.38/0.55  thf('124', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['108', '119'])).
% 0.38/0.55  thf('125', plain, ($false),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['123', '124'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
