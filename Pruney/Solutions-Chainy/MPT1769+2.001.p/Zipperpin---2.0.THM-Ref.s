%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZyPOy9uxgd

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:09 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  209 (1518 expanded)
%              Number of leaves         :   46 ( 452 expanded)
%              Depth                    :   26
%              Number of atoms          : 2164 (48573 expanded)
%              Number of equality atoms :   75 ( 798 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( m1_pre_topc @ X39 @ X41 )
      | ( ( k3_tmap_1 @ X40 @ X38 @ X41 @ X39 @ X42 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X38 ) @ X42 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( k2_tmap_1 @ X36 @ X34 @ X37 @ X35 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) @ X37 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( X28 = X32 )
      | ~ ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('82',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('85',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('86',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('91',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('94',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('103',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('117',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( sk_E
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( sk_E
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['54','119'])).

thf('121',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('122',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('123',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('124',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    r1_tarski @ sk_G @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_G @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_G ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['112'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_G @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( r1_tarski @ sk_G @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ( sk_G
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_G ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_G
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['121','134'])).

thf('136',plain,
    ( ( sk_G = sk_E )
    | ( sk_E = sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['120','135'])).

thf('137',plain,(
    sk_G = sk_E ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['138'])).

thf('140',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['137','141'])).

thf('143',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['52','142'])).

thf('144',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['138'])).

thf('146',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('149',plain,(
    sk_G = sk_E ),
    inference(simplify,[status(thm)],['136'])).

thf('150',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['147','154'])).

thf('156',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['138'])).

thf('157',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['144','155','156'])).

thf('158',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['143','157'])).

thf('159',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','158'])).

thf('160',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['144','155'])).

thf('161',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['159','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZyPOy9uxgd
% 0.14/0.38  % Computer   : n016.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 15:05:49 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 2.92/3.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.92/3.14  % Solved by: fo/fo7.sh
% 2.92/3.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.92/3.14  % done 5556 iterations in 2.649s
% 2.92/3.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.92/3.14  % SZS output start Refutation
% 2.92/3.14  thf(sk_E_type, type, sk_E: $i).
% 2.92/3.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.92/3.14  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.92/3.14  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.92/3.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.92/3.14  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 2.92/3.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.92/3.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.92/3.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.92/3.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.92/3.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.92/3.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.92/3.14  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.92/3.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.92/3.14  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.92/3.14  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.92/3.14  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.92/3.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.92/3.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.92/3.14  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.92/3.14  thf(sk_D_type, type, sk_D: $i).
% 2.92/3.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.92/3.14  thf(sk_G_type, type, sk_G: $i).
% 2.92/3.14  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 2.92/3.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.92/3.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.92/3.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.92/3.14  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.92/3.14  thf(sk_B_type, type, sk_B: $i).
% 2.92/3.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.92/3.14  thf(sk_A_type, type, sk_A: $i).
% 2.92/3.14  thf(sk_F_type, type, sk_F: $i).
% 2.92/3.14  thf(t80_tmap_1, conjecture,
% 2.92/3.14    (![A:$i]:
% 2.92/3.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.14       ( ![B:$i]:
% 2.92/3.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.92/3.14             ( l1_pre_topc @ B ) ) =>
% 2.92/3.14           ( ![C:$i]:
% 2.92/3.14             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.92/3.14               ( ![D:$i]:
% 2.92/3.14                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.92/3.14                   ( ![E:$i]:
% 2.92/3.14                     ( ( ( v1_funct_1 @ E ) & 
% 2.92/3.14                         ( v1_funct_2 @
% 2.92/3.14                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                         ( m1_subset_1 @
% 2.92/3.14                           E @ 
% 2.92/3.14                           ( k1_zfmisc_1 @
% 2.92/3.14                             ( k2_zfmisc_1 @
% 2.92/3.14                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                       ( ![F:$i]:
% 2.92/3.14                         ( ( ( v1_funct_1 @ F ) & 
% 2.92/3.14                             ( v1_funct_2 @
% 2.92/3.14                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                             ( m1_subset_1 @
% 2.92/3.14                               F @ 
% 2.92/3.14                               ( k1_zfmisc_1 @
% 2.92/3.14                                 ( k2_zfmisc_1 @
% 2.92/3.14                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                           ( ![G:$i]:
% 2.92/3.14                             ( ( ( v1_funct_1 @ G ) & 
% 2.92/3.14                                 ( v1_funct_2 @
% 2.92/3.14                                   G @ ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                   ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                                 ( m1_subset_1 @
% 2.92/3.14                                   G @ 
% 2.92/3.14                                   ( k1_zfmisc_1 @
% 2.92/3.14                                     ( k2_zfmisc_1 @
% 2.92/3.14                                       ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                               ( ( ( ( D ) = ( A ) ) & 
% 2.92/3.14                                   ( r1_funct_2 @
% 2.92/3.14                                     ( u1_struct_0 @ A ) @ 
% 2.92/3.14                                     ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                     ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 2.92/3.14                                 ( ( r2_funct_2 @
% 2.92/3.14                                     ( u1_struct_0 @ C ) @ 
% 2.92/3.14                                     ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 2.92/3.14                                   ( r2_funct_2 @
% 2.92/3.14                                     ( u1_struct_0 @ C ) @ 
% 2.92/3.14                                     ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.92/3.14  thf(zf_stmt_0, negated_conjecture,
% 2.92/3.14    (~( ![A:$i]:
% 2.92/3.14        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.92/3.14            ( l1_pre_topc @ A ) ) =>
% 2.92/3.14          ( ![B:$i]:
% 2.92/3.14            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.92/3.14                ( l1_pre_topc @ B ) ) =>
% 2.92/3.14              ( ![C:$i]:
% 2.92/3.14                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.92/3.14                  ( ![D:$i]:
% 2.92/3.14                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.92/3.14                      ( ![E:$i]:
% 2.92/3.14                        ( ( ( v1_funct_1 @ E ) & 
% 2.92/3.14                            ( v1_funct_2 @
% 2.92/3.14                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                            ( m1_subset_1 @
% 2.92/3.14                              E @ 
% 2.92/3.14                              ( k1_zfmisc_1 @
% 2.92/3.14                                ( k2_zfmisc_1 @
% 2.92/3.14                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                          ( ![F:$i]:
% 2.92/3.14                            ( ( ( v1_funct_1 @ F ) & 
% 2.92/3.14                                ( v1_funct_2 @
% 2.92/3.14                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                                ( m1_subset_1 @
% 2.92/3.14                                  F @ 
% 2.92/3.14                                  ( k1_zfmisc_1 @
% 2.92/3.14                                    ( k2_zfmisc_1 @
% 2.92/3.14                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                              ( ![G:$i]:
% 2.92/3.14                                ( ( ( v1_funct_1 @ G ) & 
% 2.92/3.14                                    ( v1_funct_2 @
% 2.92/3.14                                      G @ ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                      ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                                    ( m1_subset_1 @
% 2.92/3.14                                      G @ 
% 2.92/3.14                                      ( k1_zfmisc_1 @
% 2.92/3.14                                        ( k2_zfmisc_1 @
% 2.92/3.14                                          ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                                  ( ( ( ( D ) = ( A ) ) & 
% 2.92/3.14                                      ( r1_funct_2 @
% 2.92/3.14                                        ( u1_struct_0 @ A ) @ 
% 2.92/3.14                                        ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                        ( u1_struct_0 @ D ) @ 
% 2.92/3.14                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 2.92/3.14                                    ( ( r2_funct_2 @
% 2.92/3.14                                        ( u1_struct_0 @ C ) @ 
% 2.92/3.14                                        ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 2.92/3.14                                      ( r2_funct_2 @
% 2.92/3.14                                        ( u1_struct_0 @ C ) @ 
% 2.92/3.14                                        ( u1_struct_0 @ B ) @ 
% 2.92/3.14                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.92/3.14    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 2.92/3.14  thf('0', plain,
% 2.92/3.14      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 2.92/3.14        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('1', plain,
% 2.92/3.14      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.14         <= (~
% 2.92/3.14             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 2.92/3.14      inference('split', [status(esa)], ['0'])).
% 2.92/3.14  thf('2', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('3', plain,
% 2.92/3.14      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.14         <= (~
% 2.92/3.14             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 2.92/3.14      inference('demod', [status(thm)], ['1', '2'])).
% 2.92/3.14  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('5', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['4', '5'])).
% 2.92/3.14  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('8', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['7', '8'])).
% 2.92/3.14  thf('10', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_E @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('11', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('12', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_E @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('demod', [status(thm)], ['10', '11'])).
% 2.92/3.14  thf(d5_tmap_1, axiom,
% 2.92/3.14    (![A:$i]:
% 2.92/3.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.14       ( ![B:$i]:
% 2.92/3.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.92/3.14             ( l1_pre_topc @ B ) ) =>
% 2.92/3.14           ( ![C:$i]:
% 2.92/3.14             ( ( m1_pre_topc @ C @ A ) =>
% 2.92/3.14               ( ![D:$i]:
% 2.92/3.14                 ( ( m1_pre_topc @ D @ A ) =>
% 2.92/3.14                   ( ![E:$i]:
% 2.92/3.14                     ( ( ( v1_funct_1 @ E ) & 
% 2.92/3.14                         ( v1_funct_2 @
% 2.92/3.14                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                         ( m1_subset_1 @
% 2.92/3.14                           E @ 
% 2.92/3.14                           ( k1_zfmisc_1 @
% 2.92/3.14                             ( k2_zfmisc_1 @
% 2.92/3.14                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14                       ( ( m1_pre_topc @ D @ C ) =>
% 2.92/3.14                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 2.92/3.14                           ( k2_partfun1 @
% 2.92/3.14                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 2.92/3.14                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.92/3.14  thf('13', plain,
% 2.92/3.14      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.92/3.14         ((v2_struct_0 @ X38)
% 2.92/3.14          | ~ (v2_pre_topc @ X38)
% 2.92/3.14          | ~ (l1_pre_topc @ X38)
% 2.92/3.14          | ~ (m1_pre_topc @ X39 @ X40)
% 2.92/3.14          | ~ (m1_pre_topc @ X39 @ X41)
% 2.92/3.14          | ((k3_tmap_1 @ X40 @ X38 @ X41 @ X39 @ X42)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X38) @ 
% 2.92/3.14                 X42 @ (u1_struct_0 @ X39)))
% 2.92/3.14          | ~ (m1_subset_1 @ X42 @ 
% 2.92/3.14               (k1_zfmisc_1 @ 
% 2.92/3.14                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X38))))
% 2.92/3.14          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X38))
% 2.92/3.14          | ~ (v1_funct_1 @ X42)
% 2.92/3.14          | ~ (m1_pre_topc @ X41 @ X40)
% 2.92/3.14          | ~ (l1_pre_topc @ X40)
% 2.92/3.14          | ~ (v2_pre_topc @ X40)
% 2.92/3.14          | (v2_struct_0 @ X40))),
% 2.92/3.14      inference('cnf', [status(esa)], [d5_tmap_1])).
% 2.92/3.14  thf('14', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         ((v2_struct_0 @ X0)
% 2.92/3.14          | ~ (v2_pre_topc @ X0)
% 2.92/3.14          | ~ (l1_pre_topc @ X0)
% 2.92/3.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.92/3.14          | ~ (v1_funct_1 @ sk_E)
% 2.92/3.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 2.92/3.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X1)))
% 2.92/3.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.92/3.14          | ~ (m1_pre_topc @ X1 @ X0)
% 2.92/3.14          | ~ (l1_pre_topc @ sk_B)
% 2.92/3.14          | ~ (v2_pre_topc @ sk_B)
% 2.92/3.14          | (v2_struct_0 @ sk_B))),
% 2.92/3.14      inference('sup-', [status(thm)], ['12', '13'])).
% 2.92/3.14  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('16', plain,
% 2.92/3.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('17', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('18', plain,
% 2.92/3.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 2.92/3.14      inference('demod', [status(thm)], ['16', '17'])).
% 2.92/3.14  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('21', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         ((v2_struct_0 @ X0)
% 2.92/3.14          | ~ (v2_pre_topc @ X0)
% 2.92/3.14          | ~ (l1_pre_topc @ X0)
% 2.92/3.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 2.92/3.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X1)))
% 2.92/3.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 2.92/3.14          | ~ (m1_pre_topc @ X1 @ X0)
% 2.92/3.14          | (v2_struct_0 @ sk_B))),
% 2.92/3.14      inference('demod', [status(thm)], ['14', '15', '18', '19', '20'])).
% 2.92/3.14  thf('22', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((v2_struct_0 @ sk_B)
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X0)))
% 2.92/3.14          | ~ (l1_pre_topc @ sk_D)
% 2.92/3.14          | ~ (v2_pre_topc @ sk_D)
% 2.92/3.14          | (v2_struct_0 @ sk_D))),
% 2.92/3.14      inference('sup-', [status(thm)], ['9', '21'])).
% 2.92/3.14  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('24', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('25', plain, ((l1_pre_topc @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['23', '24'])).
% 2.92/3.14  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('27', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('28', plain, ((v2_pre_topc @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['26', '27'])).
% 2.92/3.14  thf('29', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((v2_struct_0 @ sk_B)
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X0)))
% 2.92/3.14          | (v2_struct_0 @ sk_D))),
% 2.92/3.14      inference('demod', [status(thm)], ['22', '25', '28'])).
% 2.92/3.14  thf('30', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((v2_struct_0 @ sk_D)
% 2.92/3.14          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X0)))
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | (v2_struct_0 @ sk_B))),
% 2.92/3.14      inference('simplify', [status(thm)], ['29'])).
% 2.92/3.14  thf('31', plain,
% 2.92/3.14      (((v2_struct_0 @ sk_B)
% 2.92/3.14        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 2.92/3.14            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               sk_E @ (u1_struct_0 @ sk_C_1)))
% 2.92/3.14        | (v2_struct_0 @ sk_D))),
% 2.92/3.14      inference('sup-', [status(thm)], ['6', '30'])).
% 2.92/3.14  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('33', plain,
% 2.92/3.14      (((v2_struct_0 @ sk_D)
% 2.92/3.14        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 2.92/3.14            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 2.92/3.14      inference('clc', [status(thm)], ['31', '32'])).
% 2.92/3.14  thf('34', plain, (~ (v2_struct_0 @ sk_D)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('35', plain,
% 2.92/3.14      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E)
% 2.92/3.14         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 2.92/3.14            (u1_struct_0 @ sk_C_1)))),
% 2.92/3.14      inference('clc', [status(thm)], ['33', '34'])).
% 2.92/3.14  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['4', '5'])).
% 2.92/3.14  thf('37', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_E @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('demod', [status(thm)], ['10', '11'])).
% 2.92/3.14  thf(d4_tmap_1, axiom,
% 2.92/3.14    (![A:$i]:
% 2.92/3.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.14       ( ![B:$i]:
% 2.92/3.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.92/3.14             ( l1_pre_topc @ B ) ) =>
% 2.92/3.14           ( ![C:$i]:
% 2.92/3.14             ( ( ( v1_funct_1 @ C ) & 
% 2.92/3.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.92/3.14                 ( m1_subset_1 @
% 2.92/3.14                   C @ 
% 2.92/3.14                   ( k1_zfmisc_1 @
% 2.92/3.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.92/3.14               ( ![D:$i]:
% 2.92/3.14                 ( ( m1_pre_topc @ D @ A ) =>
% 2.92/3.14                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 2.92/3.14                     ( k2_partfun1 @
% 2.92/3.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.92/3.14                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 2.92/3.14  thf('38', plain,
% 2.92/3.14      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.92/3.14         ((v2_struct_0 @ X34)
% 2.92/3.14          | ~ (v2_pre_topc @ X34)
% 2.92/3.14          | ~ (l1_pre_topc @ X34)
% 2.92/3.14          | ~ (m1_pre_topc @ X35 @ X36)
% 2.92/3.14          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 2.92/3.14                 X37 @ (u1_struct_0 @ X35)))
% 2.92/3.14          | ~ (m1_subset_1 @ X37 @ 
% 2.92/3.14               (k1_zfmisc_1 @ 
% 2.92/3.14                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 2.92/3.14          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 2.92/3.14          | ~ (v1_funct_1 @ X37)
% 2.92/3.14          | ~ (l1_pre_topc @ X36)
% 2.92/3.14          | ~ (v2_pre_topc @ X36)
% 2.92/3.14          | (v2_struct_0 @ X36))),
% 2.92/3.14      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.92/3.14  thf('39', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((v2_struct_0 @ sk_D)
% 2.92/3.14          | ~ (v2_pre_topc @ sk_D)
% 2.92/3.14          | ~ (l1_pre_topc @ sk_D)
% 2.92/3.14          | ~ (v1_funct_1 @ sk_E)
% 2.92/3.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 2.92/3.14          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X0)))
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | ~ (l1_pre_topc @ sk_B)
% 2.92/3.14          | ~ (v2_pre_topc @ sk_B)
% 2.92/3.14          | (v2_struct_0 @ sk_B))),
% 2.92/3.14      inference('sup-', [status(thm)], ['37', '38'])).
% 2.92/3.14  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['26', '27'])).
% 2.92/3.14  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 2.92/3.14      inference('demod', [status(thm)], ['23', '24'])).
% 2.92/3.14  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('43', plain,
% 2.92/3.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 2.92/3.14      inference('demod', [status(thm)], ['16', '17'])).
% 2.92/3.14  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('46', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((v2_struct_0 @ sk_D)
% 2.92/3.14          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 2.92/3.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14                 sk_E @ (u1_struct_0 @ X0)))
% 2.92/3.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 2.92/3.14          | (v2_struct_0 @ sk_B))),
% 2.92/3.14      inference('demod', [status(thm)],
% 2.92/3.14                ['39', '40', '41', '42', '43', '44', '45'])).
% 2.92/3.14  thf('47', plain,
% 2.92/3.14      (((v2_struct_0 @ sk_B)
% 2.92/3.14        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 2.92/3.14            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               sk_E @ (u1_struct_0 @ sk_C_1)))
% 2.92/3.14        | (v2_struct_0 @ sk_D))),
% 2.92/3.14      inference('sup-', [status(thm)], ['36', '46'])).
% 2.92/3.14  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('49', plain,
% 2.92/3.14      (((v2_struct_0 @ sk_D)
% 2.92/3.14        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 2.92/3.14            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 2.92/3.14      inference('clc', [status(thm)], ['47', '48'])).
% 2.92/3.14  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('51', plain,
% 2.92/3.14      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 2.92/3.14         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 2.92/3.14            (u1_struct_0 @ sk_C_1)))),
% 2.92/3.14      inference('clc', [status(thm)], ['49', '50'])).
% 2.92/3.14  thf('52', plain,
% 2.92/3.14      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 2.92/3.14         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 2.92/3.14      inference('sup+', [status(thm)], ['35', '51'])).
% 2.92/3.14  thf(t113_zfmisc_1, axiom,
% 2.92/3.14    (![A:$i,B:$i]:
% 2.92/3.14     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.92/3.14       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.92/3.14  thf('53', plain,
% 2.92/3.14      (![X9 : $i, X10 : $i]:
% 2.92/3.14         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 2.92/3.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.92/3.14  thf('54', plain,
% 2.92/3.14      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 2.92/3.14      inference('simplify', [status(thm)], ['53'])).
% 2.92/3.14  thf('55', plain,
% 2.92/3.14      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('56', plain, (((sk_D) = (sk_A))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('57', plain,
% 2.92/3.14      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.14        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 2.92/3.14      inference('demod', [status(thm)], ['55', '56'])).
% 2.92/3.14  thf('58', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_E @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('demod', [status(thm)], ['10', '11'])).
% 2.92/3.14  thf(redefinition_r1_funct_2, axiom,
% 2.92/3.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.92/3.14     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 2.92/3.14         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 2.92/3.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.92/3.14         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 2.92/3.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.92/3.14       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 2.92/3.14  thf('59', plain,
% 2.92/3.14      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.92/3.14         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.92/3.14          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 2.92/3.14          | ~ (v1_funct_1 @ X28)
% 2.92/3.14          | (v1_xboole_0 @ X31)
% 2.92/3.14          | (v1_xboole_0 @ X30)
% 2.92/3.14          | ~ (v1_funct_1 @ X32)
% 2.92/3.14          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 2.92/3.14          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 2.92/3.14          | ((X28) = (X32))
% 2.92/3.14          | ~ (r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32))),
% 2.92/3.14      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 2.92/3.14  thf('60', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.14         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 2.92/3.14             X1 @ sk_E @ X0)
% 2.92/3.14          | ((sk_E) = (X0))
% 2.92/3.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.92/3.14          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 2.92/3.14          | ~ (v1_funct_1 @ X0)
% 2.92/3.14          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14          | (v1_xboole_0 @ X1)
% 2.92/3.14          | ~ (v1_funct_1 @ sk_E)
% 2.92/3.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['58', '59'])).
% 2.92/3.14  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('62', plain,
% 2.92/3.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 2.92/3.14      inference('demod', [status(thm)], ['16', '17'])).
% 2.92/3.14  thf('63', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.14         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 2.92/3.14             X1 @ sk_E @ X0)
% 2.92/3.14          | ((sk_E) = (X0))
% 2.92/3.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.92/3.14          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 2.92/3.14          | ~ (v1_funct_1 @ X0)
% 2.92/3.14          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14          | (v1_xboole_0 @ X1))),
% 2.92/3.14      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.92/3.14  thf('64', plain,
% 2.92/3.14      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14        | ~ (v1_funct_1 @ sk_G)
% 2.92/3.14        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 2.92/3.14        | ~ (m1_subset_1 @ sk_G @ 
% 2.92/3.14             (k1_zfmisc_1 @ 
% 2.92/3.14              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 2.92/3.14        | ((sk_E) = (sk_G)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['57', '63'])).
% 2.92/3.14  thf('65', plain, ((v1_funct_1 @ sk_G)),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('66', plain,
% 2.92/3.14      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('67', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_G @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.14  thf('68', plain,
% 2.92/3.14      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.92/3.14        | ((sk_E) = (sk_G)))),
% 2.92/3.14      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 2.92/3.14  thf('69', plain,
% 2.92/3.14      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.92/3.14      inference('simplify', [status(thm)], ['68'])).
% 2.92/3.14  thf(d3_tarski, axiom,
% 2.92/3.14    (![A:$i,B:$i]:
% 2.92/3.14     ( ( r1_tarski @ A @ B ) <=>
% 2.92/3.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.92/3.14  thf('70', plain,
% 2.92/3.14      (![X1 : $i, X3 : $i]:
% 2.92/3.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.92/3.14      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.14  thf('71', plain,
% 2.92/3.14      ((m1_subset_1 @ sk_E @ 
% 2.92/3.14        (k1_zfmisc_1 @ 
% 2.92/3.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('demod', [status(thm)], ['10', '11'])).
% 2.92/3.14  thf(t3_subset, axiom,
% 2.92/3.14    (![A:$i,B:$i]:
% 2.92/3.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.92/3.14  thf('72', plain,
% 2.92/3.14      (![X11 : $i, X12 : $i]:
% 2.92/3.14         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.92/3.14      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.14  thf('73', plain,
% 2.92/3.14      ((r1_tarski @ sk_E @ 
% 2.92/3.14        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['71', '72'])).
% 2.92/3.14  thf('74', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.14         (~ (r2_hidden @ X0 @ X1)
% 2.92/3.14          | (r2_hidden @ X0 @ X2)
% 2.92/3.14          | ~ (r1_tarski @ X1 @ X2))),
% 2.92/3.14      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.14  thf('75', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((r2_hidden @ X0 @ 
% 2.92/3.14           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 2.92/3.14          | ~ (r2_hidden @ X0 @ sk_E))),
% 2.92/3.14      inference('sup-', [status(thm)], ['73', '74'])).
% 2.92/3.14  thf('76', plain,
% 2.92/3.14      (![X0 : $i]:
% 2.92/3.14         ((r1_tarski @ sk_E @ X0)
% 2.92/3.14          | (r2_hidden @ (sk_C @ X0 @ sk_E) @ 
% 2.92/3.14             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.14      inference('sup-', [status(thm)], ['70', '75'])).
% 2.92/3.14  thf('77', plain,
% 2.92/3.14      (![X1 : $i, X3 : $i]:
% 2.92/3.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.92/3.14      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.14  thf(d10_xboole_0, axiom,
% 2.92/3.14    (![A:$i,B:$i]:
% 2.92/3.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.92/3.14  thf('78', plain,
% 2.92/3.14      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.92/3.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.92/3.14  thf('79', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.92/3.14      inference('simplify', [status(thm)], ['78'])).
% 2.92/3.14  thf('80', plain,
% 2.92/3.14      (![X11 : $i, X13 : $i]:
% 2.92/3.14         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 2.92/3.14      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.14  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['79', '80'])).
% 2.92/3.14  thf(t5_subset, axiom,
% 2.92/3.14    (![A:$i,B:$i,C:$i]:
% 2.92/3.14     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.92/3.14          ( v1_xboole_0 @ C ) ) ))).
% 2.92/3.14  thf('82', plain,
% 2.92/3.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.92/3.14         (~ (r2_hidden @ X14 @ X15)
% 2.92/3.14          | ~ (v1_xboole_0 @ X16)
% 2.92/3.14          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.92/3.14      inference('cnf', [status(esa)], [t5_subset])).
% 2.92/3.14  thf('83', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['81', '82'])).
% 2.92/3.14  thf('84', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['77', '83'])).
% 2.92/3.14  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.92/3.14  thf('85', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 2.92/3.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.92/3.14  thf('86', plain,
% 2.92/3.14      (![X4 : $i, X6 : $i]:
% 2.92/3.14         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.92/3.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.92/3.14  thf('87', plain,
% 2.92/3.14      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['85', '86'])).
% 2.92/3.14  thf('88', plain,
% 2.92/3.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['84', '87'])).
% 2.92/3.14  thf('89', plain,
% 2.92/3.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['84', '87'])).
% 2.92/3.14  thf('90', plain,
% 2.92/3.14      (![X9 : $i, X10 : $i]:
% 2.92/3.14         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 2.92/3.14      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.92/3.14  thf('91', plain,
% 2.92/3.14      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 2.92/3.14      inference('simplify', [status(thm)], ['90'])).
% 2.92/3.14  thf('92', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.92/3.14      inference('sup+', [status(thm)], ['89', '91'])).
% 2.92/3.14  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['79', '80'])).
% 2.92/3.14  thf(cc2_relset_1, axiom,
% 2.92/3.14    (![A:$i,B:$i,C:$i]:
% 2.92/3.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.92/3.14       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.92/3.14  thf('94', plain,
% 2.92/3.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.92/3.14         ((v5_relat_1 @ X22 @ X24)
% 2.92/3.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.92/3.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.92/3.14  thf('95', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 2.92/3.14      inference('sup-', [status(thm)], ['93', '94'])).
% 2.92/3.14  thf(d19_relat_1, axiom,
% 2.92/3.14    (![A:$i,B:$i]:
% 2.92/3.14     ( ( v1_relat_1 @ B ) =>
% 2.92/3.14       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.92/3.14  thf('96', plain,
% 2.92/3.14      (![X17 : $i, X18 : $i]:
% 2.92/3.14         (~ (v5_relat_1 @ X17 @ X18)
% 2.92/3.14          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 2.92/3.14          | ~ (v1_relat_1 @ X17))),
% 2.92/3.14      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.92/3.14  thf('97', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.92/3.14          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['95', '96'])).
% 2.92/3.14  thf('98', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['79', '80'])).
% 2.92/3.14  thf(cc1_relset_1, axiom,
% 2.92/3.14    (![A:$i,B:$i,C:$i]:
% 2.92/3.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.92/3.14       ( v1_relat_1 @ C ) ))).
% 2.92/3.14  thf('99', plain,
% 2.92/3.14      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.92/3.14         ((v1_relat_1 @ X19)
% 2.92/3.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.92/3.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.92/3.14  thf('100', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['98', '99'])).
% 2.92/3.14  thf('101', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 2.92/3.14      inference('demod', [status(thm)], ['97', '100'])).
% 2.92/3.14  thf('102', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.92/3.14      inference('simplify', [status(thm)], ['78'])).
% 2.92/3.14  thf(t11_relset_1, axiom,
% 2.92/3.14    (![A:$i,B:$i,C:$i]:
% 2.92/3.14     ( ( v1_relat_1 @ C ) =>
% 2.92/3.14       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 2.92/3.14           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 2.92/3.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.92/3.14  thf('103', plain,
% 2.92/3.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.92/3.14         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 2.92/3.14          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 2.92/3.14          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.92/3.14          | ~ (v1_relat_1 @ X25))),
% 2.92/3.14      inference('cnf', [status(esa)], [t11_relset_1])).
% 2.92/3.14  thf('104', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         (~ (v1_relat_1 @ X0)
% 2.92/3.14          | (m1_subset_1 @ X0 @ 
% 2.92/3.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 2.92/3.14          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.92/3.14      inference('sup-', [status(thm)], ['102', '103'])).
% 2.92/3.14  thf('105', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 2.92/3.14           (k1_zfmisc_1 @ 
% 2.92/3.14            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))
% 2.92/3.14          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['101', '104'])).
% 2.92/3.14  thf('106', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 2.92/3.14      inference('sup-', [status(thm)], ['98', '99'])).
% 2.92/3.14  thf('107', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 2.92/3.14          (k1_zfmisc_1 @ 
% 2.92/3.14           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))),
% 2.92/3.14      inference('demod', [status(thm)], ['105', '106'])).
% 2.92/3.14  thf('108', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i]:
% 2.92/3.14         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.92/3.14          | ~ (v1_xboole_0 @ X0))),
% 2.92/3.14      inference('sup+', [status(thm)], ['92', '107'])).
% 2.92/3.14  thf('109', plain,
% 2.92/3.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.92/3.14         (~ (r2_hidden @ X14 @ X15)
% 2.92/3.14          | ~ (v1_xboole_0 @ X16)
% 2.92/3.14          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.92/3.14      inference('cnf', [status(esa)], [t5_subset])).
% 2.92/3.14  thf('110', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.14         (~ (v1_xboole_0 @ X0)
% 2.92/3.14          | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.92/3.14          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 2.92/3.14      inference('sup-', [status(thm)], ['108', '109'])).
% 2.92/3.14  thf('111', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.92/3.14         (~ (v1_xboole_0 @ X0)
% 2.92/3.14          | ~ (v1_xboole_0 @ X0)
% 2.92/3.14          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X1))
% 2.92/3.14          | ~ (v1_xboole_0 @ X1))),
% 2.92/3.14      inference('sup-', [status(thm)], ['88', '110'])).
% 2.92/3.14  thf('112', plain,
% 2.92/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.92/3.14         (~ (v1_xboole_0 @ X1)
% 2.92/3.14          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X1))
% 2.92/3.15          | ~ (v1_xboole_0 @ X0))),
% 2.92/3.15      inference('simplify', [status(thm)], ['111'])).
% 2.92/3.15  thf('113', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.15         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 2.92/3.15      inference('condensation', [status(thm)], ['112'])).
% 2.92/3.15  thf('114', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         ((r1_tarski @ sk_E @ X0) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.92/3.15      inference('sup-', [status(thm)], ['76', '113'])).
% 2.92/3.15  thf('115', plain,
% 2.92/3.15      (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_E @ X0))),
% 2.92/3.15      inference('sup-', [status(thm)], ['69', '114'])).
% 2.92/3.15  thf('116', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i]:
% 2.92/3.15         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 2.92/3.15      inference('demod', [status(thm)], ['97', '100'])).
% 2.92/3.15  thf('117', plain,
% 2.92/3.15      (![X4 : $i, X6 : $i]:
% 2.92/3.15         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.92/3.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.92/3.15  thf('118', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i]:
% 2.92/3.15         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.92/3.15          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 2.92/3.15      inference('sup-', [status(thm)], ['116', '117'])).
% 2.92/3.15  thf('119', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         (((sk_E) = (sk_G))
% 2.92/3.15          | ((sk_E) = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_E))))),
% 2.92/3.15      inference('sup-', [status(thm)], ['115', '118'])).
% 2.92/3.15  thf('120', plain,
% 2.92/3.15      ((((sk_E) = (k2_relat_1 @ k1_xboole_0)) | ((sk_E) = (sk_G)))),
% 2.92/3.15      inference('sup+', [status(thm)], ['54', '119'])).
% 2.92/3.15  thf('121', plain,
% 2.92/3.15      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 2.92/3.15      inference('simplify', [status(thm)], ['53'])).
% 2.92/3.15  thf('122', plain,
% 2.92/3.15      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.92/3.15      inference('simplify', [status(thm)], ['68'])).
% 2.92/3.15  thf('123', plain,
% 2.92/3.15      (![X1 : $i, X3 : $i]:
% 2.92/3.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.92/3.15      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.15  thf('124', plain,
% 2.92/3.15      ((m1_subset_1 @ sk_G @ 
% 2.92/3.15        (k1_zfmisc_1 @ 
% 2.92/3.15         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.15  thf('125', plain,
% 2.92/3.15      (![X11 : $i, X12 : $i]:
% 2.92/3.15         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.92/3.15      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.15  thf('126', plain,
% 2.92/3.15      ((r1_tarski @ sk_G @ 
% 2.92/3.15        (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 2.92/3.15      inference('sup-', [status(thm)], ['124', '125'])).
% 2.92/3.15  thf('127', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.15         (~ (r2_hidden @ X0 @ X1)
% 2.92/3.15          | (r2_hidden @ X0 @ X2)
% 2.92/3.15          | ~ (r1_tarski @ X1 @ X2))),
% 2.92/3.15      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.15  thf('128', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         ((r2_hidden @ X0 @ 
% 2.92/3.15           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 2.92/3.15          | ~ (r2_hidden @ X0 @ sk_G))),
% 2.92/3.15      inference('sup-', [status(thm)], ['126', '127'])).
% 2.92/3.15  thf('129', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         ((r1_tarski @ sk_G @ X0)
% 2.92/3.15          | (r2_hidden @ (sk_C @ X0 @ sk_G) @ 
% 2.92/3.15             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 2.92/3.15      inference('sup-', [status(thm)], ['123', '128'])).
% 2.92/3.15  thf('130', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.15         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 2.92/3.15      inference('condensation', [status(thm)], ['112'])).
% 2.92/3.15  thf('131', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         ((r1_tarski @ sk_G @ X0) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.92/3.15      inference('sup-', [status(thm)], ['129', '130'])).
% 2.92/3.15  thf('132', plain,
% 2.92/3.15      (![X0 : $i]: (((sk_E) = (sk_G)) | (r1_tarski @ sk_G @ X0))),
% 2.92/3.15      inference('sup-', [status(thm)], ['122', '131'])).
% 2.92/3.15  thf('133', plain,
% 2.92/3.15      (![X0 : $i, X1 : $i]:
% 2.92/3.15         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.92/3.15          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 2.92/3.15      inference('sup-', [status(thm)], ['116', '117'])).
% 2.92/3.15  thf('134', plain,
% 2.92/3.15      (![X0 : $i]:
% 2.92/3.15         (((sk_E) = (sk_G))
% 2.92/3.15          | ((sk_G) = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_G))))),
% 2.92/3.15      inference('sup-', [status(thm)], ['132', '133'])).
% 2.92/3.15  thf('135', plain,
% 2.92/3.15      ((((sk_G) = (k2_relat_1 @ k1_xboole_0)) | ((sk_E) = (sk_G)))),
% 2.92/3.15      inference('sup+', [status(thm)], ['121', '134'])).
% 2.92/3.15  thf('136', plain,
% 2.92/3.15      ((((sk_G) = (sk_E)) | ((sk_E) = (sk_G)) | ((sk_E) = (sk_G)))),
% 2.92/3.15      inference('sup+', [status(thm)], ['120', '135'])).
% 2.92/3.15  thf('137', plain, (((sk_G) = (sk_E))),
% 2.92/3.15      inference('simplify', [status(thm)], ['136'])).
% 2.92/3.15  thf('138', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)
% 2.92/3.15        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 2.92/3.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.15  thf('139', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('split', [status(esa)], ['138'])).
% 2.92/3.15  thf('140', plain, (((sk_D) = (sk_A))),
% 2.92/3.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.15  thf('141', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('demod', [status(thm)], ['139', '140'])).
% 2.92/3.15  thf('142', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('sup+', [status(thm)], ['137', '141'])).
% 2.92/3.15  thf('143', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('sup+', [status(thm)], ['52', '142'])).
% 2.92/3.15  thf('144', plain,
% 2.92/3.15      (~
% 2.92/3.15       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)) | 
% 2.92/3.15       ~
% 2.92/3.15       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 2.92/3.15      inference('split', [status(esa)], ['0'])).
% 2.92/3.15  thf('145', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 2.92/3.15      inference('split', [status(esa)], ['138'])).
% 2.92/3.15  thf('146', plain, (((sk_D) = (sk_A))),
% 2.92/3.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.15  thf('147', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.15         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 2.92/3.15      inference('demod', [status(thm)], ['145', '146'])).
% 2.92/3.15  thf('148', plain,
% 2.92/3.15      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1)
% 2.92/3.15         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E))),
% 2.92/3.15      inference('sup+', [status(thm)], ['35', '51'])).
% 2.92/3.15  thf('149', plain, (((sk_G) = (sk_E))),
% 2.92/3.15      inference('simplify', [status(thm)], ['136'])).
% 2.92/3.15  thf('150', plain,
% 2.92/3.15      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 2.92/3.15         <= (~
% 2.92/3.15             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('split', [status(esa)], ['0'])).
% 2.92/3.15  thf('151', plain, (((sk_D) = (sk_A))),
% 2.92/3.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.15  thf('152', plain,
% 2.92/3.15      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 2.92/3.15         <= (~
% 2.92/3.15             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('demod', [status(thm)], ['150', '151'])).
% 2.92/3.15  thf('153', plain,
% 2.92/3.15      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 2.92/3.15         <= (~
% 2.92/3.15             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('sup-', [status(thm)], ['149', '152'])).
% 2.92/3.15  thf('154', plain,
% 2.92/3.15      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F))
% 2.92/3.15         <= (~
% 2.92/3.15             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 2.92/3.15      inference('sup-', [status(thm)], ['148', '153'])).
% 2.92/3.15  thf('155', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 2.92/3.15       ~
% 2.92/3.15       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 2.92/3.15      inference('sup-', [status(thm)], ['147', '154'])).
% 2.92/3.15  thf('156', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 2.92/3.15       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 2.92/3.15      inference('split', [status(esa)], ['138'])).
% 2.92/3.15  thf('157', plain,
% 2.92/3.15      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 2.92/3.15      inference('sat_resolution*', [status(thm)], ['144', '155', '156'])).
% 2.92/3.15  thf('158', plain,
% 2.92/3.15      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15        (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C_1) @ sk_F)),
% 2.92/3.15      inference('simpl_trail', [status(thm)], ['143', '157'])).
% 2.92/3.15  thf('159', plain,
% 2.92/3.15      (($false)
% 2.92/3.15         <= (~
% 2.92/3.15             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F)))),
% 2.92/3.15      inference('demod', [status(thm)], ['3', '158'])).
% 2.92/3.15  thf('160', plain,
% 2.92/3.15      (~
% 2.92/3.15       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 2.92/3.15         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1) @ sk_F))),
% 2.92/3.15      inference('sat_resolution*', [status(thm)], ['144', '155'])).
% 2.92/3.15  thf('161', plain, ($false),
% 2.92/3.15      inference('simpl_trail', [status(thm)], ['159', '160'])).
% 2.92/3.15  
% 2.92/3.15  % SZS output end Refutation
% 2.92/3.15  
% 2.92/3.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
