%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YS7a3HseFq

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:11 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 869 expanded)
%              Number of leaves         :   38 ( 256 expanded)
%              Depth                    :   23
%              Number of atoms          : 1796 (45633 expanded)
%              Number of equality atoms :   57 ( 585 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('7',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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
    inference(demod,[status(thm)],['12','13','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','23','24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','22'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['34','50'])).

thf('52',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( X14 = X18 )
      | ~ ( r1_funct_2 @ X15 @ X16 @ X19 @ X17 @ X14 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,
    ( ( sk_E = sk_G )
    | ( ( sk_B @ sk_B_1 )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_E = sk_G )
    | ( ( sk_B @ sk_B_1 )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_E = sk_G ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( sk_E = sk_G )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('91',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['96','100'])).

thf('102',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['51','101'])).

thf('103',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['97'])).

thf('105',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['34','50'])).

thf('108',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['94','95'])).

thf('109',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('110',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['97'])).

thf('116',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['103','114','115'])).

thf('117',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['102','116'])).

thf('118',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','117'])).

thf('119',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['103','114'])).

thf('120',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YS7a3HseFq
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:57:19 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.06  % Solved by: fo/fo7.sh
% 0.90/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.06  % done 1029 iterations in 0.594s
% 0.90/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.06  % SZS output start Refutation
% 0.90/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.06  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.06  thf(sk_G_type, type, sk_G: $i).
% 0.90/1.06  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.90/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.06  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.06  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.90/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.06  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.90/1.06  thf(sk_F_type, type, sk_F: $i).
% 0.90/1.06  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.90/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.06  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.90/1.06  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.90/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.06  thf(t80_tmap_1, conjecture,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.06             ( l1_pre_topc @ B ) ) =>
% 0.90/1.06           ( ![C:$i]:
% 0.90/1.06             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.06               ( ![D:$i]:
% 0.90/1.06                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.06                   ( ![E:$i]:
% 0.90/1.06                     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.06                         ( v1_funct_2 @
% 0.90/1.06                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                         ( m1_subset_1 @
% 0.90/1.06                           E @ 
% 0.90/1.06                           ( k1_zfmisc_1 @
% 0.90/1.06                             ( k2_zfmisc_1 @
% 0.90/1.06                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                       ( ![F:$i]:
% 0.90/1.06                         ( ( ( v1_funct_1 @ F ) & 
% 0.90/1.06                             ( v1_funct_2 @
% 0.90/1.06                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                             ( m1_subset_1 @
% 0.90/1.06                               F @ 
% 0.90/1.06                               ( k1_zfmisc_1 @
% 0.90/1.06                                 ( k2_zfmisc_1 @
% 0.90/1.06                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                           ( ![G:$i]:
% 0.90/1.06                             ( ( ( v1_funct_1 @ G ) & 
% 0.90/1.06                                 ( v1_funct_2 @
% 0.90/1.06                                   G @ ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                   ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                                 ( m1_subset_1 @
% 0.90/1.06                                   G @ 
% 0.90/1.06                                   ( k1_zfmisc_1 @
% 0.90/1.06                                     ( k2_zfmisc_1 @
% 0.90/1.06                                       ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                               ( ( ( ( D ) = ( A ) ) & 
% 0.90/1.06                                   ( r1_funct_2 @
% 0.90/1.06                                     ( u1_struct_0 @ A ) @ 
% 0.90/1.06                                     ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                     ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.90/1.06                                 ( ( r2_funct_2 @
% 0.90/1.06                                     ( u1_struct_0 @ C ) @ 
% 0.90/1.06                                     ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.90/1.06                                   ( r2_funct_2 @
% 0.90/1.06                                     ( u1_struct_0 @ C ) @ 
% 0.90/1.06                                     ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.06    (~( ![A:$i]:
% 0.90/1.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.06            ( l1_pre_topc @ A ) ) =>
% 0.90/1.06          ( ![B:$i]:
% 0.90/1.06            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.06                ( l1_pre_topc @ B ) ) =>
% 0.90/1.06              ( ![C:$i]:
% 0.90/1.06                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.06                  ( ![D:$i]:
% 0.90/1.06                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.06                      ( ![E:$i]:
% 0.90/1.06                        ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.06                            ( v1_funct_2 @
% 0.90/1.06                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                            ( m1_subset_1 @
% 0.90/1.06                              E @ 
% 0.90/1.06                              ( k1_zfmisc_1 @
% 0.90/1.06                                ( k2_zfmisc_1 @
% 0.90/1.06                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                          ( ![F:$i]:
% 0.90/1.06                            ( ( ( v1_funct_1 @ F ) & 
% 0.90/1.06                                ( v1_funct_2 @
% 0.90/1.06                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                                ( m1_subset_1 @
% 0.90/1.06                                  F @ 
% 0.90/1.06                                  ( k1_zfmisc_1 @
% 0.90/1.06                                    ( k2_zfmisc_1 @
% 0.90/1.06                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                              ( ![G:$i]:
% 0.90/1.06                                ( ( ( v1_funct_1 @ G ) & 
% 0.90/1.06                                    ( v1_funct_2 @
% 0.90/1.06                                      G @ ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                      ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                                    ( m1_subset_1 @
% 0.90/1.06                                      G @ 
% 0.90/1.06                                      ( k1_zfmisc_1 @
% 0.90/1.06                                        ( k2_zfmisc_1 @
% 0.90/1.06                                          ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                                  ( ( ( ( D ) = ( A ) ) & 
% 0.90/1.06                                      ( r1_funct_2 @
% 0.90/1.06                                        ( u1_struct_0 @ A ) @ 
% 0.90/1.06                                        ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                        ( u1_struct_0 @ D ) @ 
% 0.90/1.06                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.90/1.06                                    ( ( r2_funct_2 @
% 0.90/1.06                                        ( u1_struct_0 @ C ) @ 
% 0.90/1.06                                        ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.90/1.06                                      ( r2_funct_2 @
% 0.90/1.06                                        ( u1_struct_0 @ C ) @ 
% 0.90/1.06                                        ( u1_struct_0 @ B ) @ 
% 0.90/1.06                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.06    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.90/1.06  thf('0', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 0.90/1.06        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06             (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('1', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.90/1.06      inference('split', [status(esa)], ['0'])).
% 0.90/1.06  thf('2', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('3', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.90/1.06      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.06  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('5', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['4', '5'])).
% 0.90/1.06  thf(t2_tsep_1, axiom,
% 0.90/1.06    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.90/1.06  thf('7', plain,
% 0.90/1.06      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.90/1.06      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.06  thf('8', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_E @ 
% 0.90/1.06        (k1_zfmisc_1 @ 
% 0.90/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('9', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('10', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_E @ 
% 0.90/1.06        (k1_zfmisc_1 @ 
% 0.90/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.90/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf(d5_tmap_1, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.06             ( l1_pre_topc @ B ) ) =>
% 0.90/1.06           ( ![C:$i]:
% 0.90/1.06             ( ( m1_pre_topc @ C @ A ) =>
% 0.90/1.06               ( ![D:$i]:
% 0.90/1.06                 ( ( m1_pre_topc @ D @ A ) =>
% 0.90/1.06                   ( ![E:$i]:
% 0.90/1.06                     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.06                         ( v1_funct_2 @
% 0.90/1.06                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                         ( m1_subset_1 @
% 0.90/1.06                           E @ 
% 0.90/1.06                           ( k1_zfmisc_1 @
% 0.90/1.06                             ( k2_zfmisc_1 @
% 0.90/1.06                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06                       ( ( m1_pre_topc @ D @ C ) =>
% 0.90/1.06                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.90/1.06                           ( k2_partfun1 @
% 0.90/1.06                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.90/1.06                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.06  thf('11', plain,
% 0.90/1.06      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.06         ((v2_struct_0 @ X24)
% 0.90/1.06          | ~ (v2_pre_topc @ X24)
% 0.90/1.06          | ~ (l1_pre_topc @ X24)
% 0.90/1.06          | ~ (m1_pre_topc @ X25 @ X26)
% 0.90/1.06          | ~ (m1_pre_topc @ X25 @ X27)
% 0.90/1.06          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.90/1.06                 X28 @ (u1_struct_0 @ X25)))
% 0.90/1.06          | ~ (m1_subset_1 @ X28 @ 
% 0.90/1.06               (k1_zfmisc_1 @ 
% 0.90/1.06                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.90/1.06          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.90/1.06          | ~ (v1_funct_1 @ X28)
% 0.90/1.06          | ~ (m1_pre_topc @ X27 @ X26)
% 0.90/1.06          | ~ (l1_pre_topc @ X26)
% 0.90/1.06          | ~ (v2_pre_topc @ X26)
% 0.90/1.06          | (v2_struct_0 @ X26))),
% 0.90/1.06      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.90/1.06  thf('12', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((v2_struct_0 @ X0)
% 0.90/1.06          | ~ (v2_pre_topc @ X0)
% 0.90/1.06          | ~ (l1_pre_topc @ X0)
% 0.90/1.06          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.06          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.06          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.90/1.06               (u1_struct_0 @ sk_B_1))
% 0.90/1.06          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X1)))
% 0.90/1.06          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.06          | ~ (m1_pre_topc @ X1 @ X0)
% 0.90/1.06          | ~ (l1_pre_topc @ sk_B_1)
% 0.90/1.06          | ~ (v2_pre_topc @ sk_B_1)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.06  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('14', plain,
% 0.90/1.06      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('15', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('16', plain,
% 0.90/1.06      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.06  thf('17', plain, ((l1_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('18', plain, ((v2_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('19', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((v2_struct_0 @ X0)
% 0.90/1.06          | ~ (v2_pre_topc @ X0)
% 0.90/1.06          | ~ (l1_pre_topc @ X0)
% 0.90/1.06          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.06          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X1)))
% 0.90/1.06          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.06          | ~ (m1_pre_topc @ X1 @ X0)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['12', '13', '16', '17', '18'])).
% 0.90/1.06  thf('20', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         (~ (l1_pre_topc @ sk_D)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1)
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.06          | ~ (l1_pre_topc @ sk_D)
% 0.90/1.06          | ~ (v2_pre_topc @ sk_D)
% 0.90/1.06          | (v2_struct_0 @ sk_D))),
% 0.90/1.06      inference('sup-', [status(thm)], ['7', '19'])).
% 0.90/1.06  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('22', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.06  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.06  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('26', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('27', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['25', '26'])).
% 0.90/1.06  thf('28', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ sk_B_1)
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.06          | (v2_struct_0 @ sk_D))),
% 0.90/1.06      inference('demod', [status(thm)], ['20', '23', '24', '27'])).
% 0.90/1.06  thf('29', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ sk_D)
% 0.90/1.06          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('simplify', [status(thm)], ['28'])).
% 0.90/1.06  thf('30', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_B_1)
% 0.90/1.06        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.90/1.06            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.06        | (v2_struct_0 @ sk_D))),
% 0.90/1.06      inference('sup-', [status(thm)], ['6', '29'])).
% 0.90/1.06  thf('31', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('32', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_D)
% 0.90/1.06        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.90/1.06            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.90/1.06      inference('clc', [status(thm)], ['30', '31'])).
% 0.90/1.06  thf('33', plain, (~ (v2_struct_0 @ sk_D)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('34', plain,
% 0.90/1.06      (((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.90/1.06         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 0.90/1.06      inference('clc', [status(thm)], ['32', '33'])).
% 0.90/1.06  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['4', '5'])).
% 0.90/1.06  thf('36', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_E @ 
% 0.90/1.06        (k1_zfmisc_1 @ 
% 0.90/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.90/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf(d4_tmap_1, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.06             ( l1_pre_topc @ B ) ) =>
% 0.90/1.06           ( ![C:$i]:
% 0.90/1.06             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.06                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.06                 ( m1_subset_1 @
% 0.90/1.06                   C @ 
% 0.90/1.06                   ( k1_zfmisc_1 @
% 0.90/1.06                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.06               ( ![D:$i]:
% 0.90/1.06                 ( ( m1_pre_topc @ D @ A ) =>
% 0.90/1.06                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.90/1.06                     ( k2_partfun1 @
% 0.90/1.06                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.90/1.06                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.06  thf('37', plain,
% 0.90/1.06      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.06         ((v2_struct_0 @ X20)
% 0.90/1.06          | ~ (v2_pre_topc @ X20)
% 0.90/1.06          | ~ (l1_pre_topc @ X20)
% 0.90/1.06          | ~ (m1_pre_topc @ X21 @ X22)
% 0.90/1.06          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.90/1.06                 X23 @ (u1_struct_0 @ X21)))
% 0.90/1.06          | ~ (m1_subset_1 @ X23 @ 
% 0.90/1.06               (k1_zfmisc_1 @ 
% 0.90/1.06                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.90/1.06          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.90/1.06          | ~ (v1_funct_1 @ X23)
% 0.90/1.06          | ~ (l1_pre_topc @ X22)
% 0.90/1.06          | ~ (v2_pre_topc @ X22)
% 0.90/1.06          | (v2_struct_0 @ X22))),
% 0.90/1.06      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.90/1.06  thf('38', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ sk_D)
% 0.90/1.06          | ~ (v2_pre_topc @ sk_D)
% 0.90/1.06          | ~ (l1_pre_topc @ sk_D)
% 0.90/1.06          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.06          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.90/1.06               (u1_struct_0 @ sk_B_1))
% 0.90/1.06          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | ~ (l1_pre_topc @ sk_B_1)
% 0.90/1.06          | ~ (v2_pre_topc @ sk_B_1)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.06  thf('39', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['25', '26'])).
% 0.90/1.06  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.06  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('42', plain,
% 0.90/1.06      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.06  thf('43', plain, ((l1_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('44', plain, ((v2_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('45', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ sk_D)
% 0.90/1.06          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.90/1.06              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.06          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.06          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)],
% 0.90/1.06                ['38', '39', '40', '41', '42', '43', '44'])).
% 0.90/1.06  thf('46', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_B_1)
% 0.90/1.06        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.90/1.06            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.90/1.06        | (v2_struct_0 @ sk_D))),
% 0.90/1.06      inference('sup-', [status(thm)], ['35', '45'])).
% 0.90/1.06  thf('47', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('48', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_D)
% 0.90/1.06        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.90/1.06            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.90/1.06      inference('clc', [status(thm)], ['46', '47'])).
% 0.90/1.06  thf('49', plain, (~ (v2_struct_0 @ sk_D)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('50', plain,
% 0.90/1.06      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.90/1.06         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 0.90/1.06      inference('clc', [status(thm)], ['48', '49'])).
% 0.90/1.06  thf('51', plain,
% 0.90/1.06      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.90/1.06         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 0.90/1.06      inference('sup+', [status(thm)], ['34', '50'])).
% 0.90/1.06  thf('52', plain,
% 0.90/1.06      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('53', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('54', plain,
% 0.90/1.06      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.90/1.06      inference('demod', [status(thm)], ['52', '53'])).
% 0.90/1.06  thf('55', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_E @ 
% 0.90/1.06        (k1_zfmisc_1 @ 
% 0.90/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.90/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf(redefinition_r1_funct_2, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.06     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.90/1.06         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.90/1.06         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.06         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.90/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.06       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.90/1.06  thf('56', plain,
% 0.90/1.06      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.90/1.06         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.90/1.06          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.90/1.06          | ~ (v1_funct_1 @ X14)
% 0.90/1.06          | (v1_xboole_0 @ X17)
% 0.90/1.06          | (v1_xboole_0 @ X16)
% 0.90/1.06          | ~ (v1_funct_1 @ X18)
% 0.90/1.06          | ~ (v1_funct_2 @ X18 @ X19 @ X17)
% 0.90/1.06          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 0.90/1.06          | ((X14) = (X18))
% 0.90/1.06          | ~ (r1_funct_2 @ X15 @ X16 @ X19 @ X17 @ X14 @ X18))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.90/1.06  thf('57', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.90/1.06             X1 @ sk_E @ X0)
% 0.90/1.06          | ((sk_E) = (X0))
% 0.90/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.06          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.90/1.06          | ~ (v1_funct_1 @ X0)
% 0.90/1.06          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06          | (v1_xboole_0 @ X1)
% 0.90/1.06          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.06          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.90/1.06               (u1_struct_0 @ sk_B_1)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.06  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('59', plain,
% 0.90/1.06      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.06  thf('60', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.90/1.06             X1 @ sk_E @ X0)
% 0.90/1.06          | ((sk_E) = (X0))
% 0.90/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.06          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.90/1.06          | ~ (v1_funct_1 @ X0)
% 0.90/1.06          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06          | (v1_xboole_0 @ X1))),
% 0.90/1.06      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.06  thf('61', plain,
% 0.90/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | ~ (v1_funct_1 @ sk_G)
% 0.90/1.06        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | ~ (m1_subset_1 @ sk_G @ 
% 0.90/1.06             (k1_zfmisc_1 @ 
% 0.90/1.06              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))
% 0.90/1.06        | ((sk_E) = (sk_G)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['54', '60'])).
% 0.90/1.06  thf('62', plain, ((v1_funct_1 @ sk_G)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('63', plain,
% 0.90/1.06      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('64', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_G @ 
% 0.90/1.06        (k1_zfmisc_1 @ 
% 0.90/1.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('65', plain,
% 0.90/1.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | ((sk_E) = (sk_G)))),
% 0.90/1.06      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.90/1.06  thf('66', plain,
% 0.90/1.06      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.90/1.06      inference('simplify', [status(thm)], ['65'])).
% 0.90/1.06  thf(rc7_pre_topc, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.06       ( ?[B:$i]:
% 0.90/1.06         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.90/1.06           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.90/1.06  thf('67', plain,
% 0.90/1.06      (![X13 : $i]:
% 0.90/1.06         ((m1_subset_1 @ (sk_B @ X13) @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.90/1.06          | ~ (l1_pre_topc @ X13)
% 0.90/1.06          | ~ (v2_pre_topc @ X13)
% 0.90/1.06          | (v2_struct_0 @ X13))),
% 0.90/1.06      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.90/1.06  thf(t3_subset, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.06  thf('68', plain,
% 0.90/1.06      (![X7 : $i, X8 : $i]:
% 0.90/1.06         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.06  thf('69', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ X0)
% 0.90/1.06          | ~ (v2_pre_topc @ X0)
% 0.90/1.06          | ~ (l1_pre_topc @ X0)
% 0.90/1.06          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.06  thf(d3_tarski, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.06  thf('70', plain,
% 0.90/1.06      (![X1 : $i, X3 : $i]:
% 0.90/1.06         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.90/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.06  thf(d10_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.06  thf('71', plain,
% 0.90/1.06      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.06  thf('72', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.06      inference('simplify', [status(thm)], ['71'])).
% 0.90/1.06  thf('73', plain,
% 0.90/1.06      (![X7 : $i, X9 : $i]:
% 0.90/1.06         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.06  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.06  thf(t5_subset, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.90/1.06          ( v1_xboole_0 @ C ) ) ))).
% 0.90/1.06  thf('75', plain,
% 0.90/1.06      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X10 @ X11)
% 0.90/1.06          | ~ (v1_xboole_0 @ X12)
% 0.90/1.06          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t5_subset])).
% 0.90/1.06  thf('76', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.06  thf('77', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['70', '76'])).
% 0.90/1.06  thf('78', plain,
% 0.90/1.06      (![X4 : $i, X6 : $i]:
% 0.90/1.06         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.06  thf('79', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.06  thf('80', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         (~ (l1_pre_topc @ X0)
% 0.90/1.06          | ~ (v2_pre_topc @ X0)
% 0.90/1.06          | (v2_struct_0 @ X0)
% 0.90/1.06          | ((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.90/1.06          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['69', '79'])).
% 0.90/1.06  thf('81', plain,
% 0.90/1.06      ((((sk_E) = (sk_G))
% 0.90/1.06        | ((sk_B @ sk_B_1) = (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | (v2_struct_0 @ sk_B_1)
% 0.90/1.06        | ~ (v2_pre_topc @ sk_B_1)
% 0.90/1.06        | ~ (l1_pre_topc @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['66', '80'])).
% 0.90/1.06  thf('82', plain, ((v2_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('83', plain, ((l1_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('84', plain,
% 0.90/1.06      ((((sk_E) = (sk_G))
% 0.90/1.06        | ((sk_B @ sk_B_1) = (u1_struct_0 @ sk_B_1))
% 0.90/1.06        | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.90/1.06  thf('85', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('86', plain,
% 0.90/1.06      ((((sk_B @ sk_B_1) = (u1_struct_0 @ sk_B_1)) | ((sk_E) = (sk_G)))),
% 0.90/1.06      inference('clc', [status(thm)], ['84', '85'])).
% 0.90/1.06  thf('87', plain,
% 0.90/1.06      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.90/1.06      inference('simplify', [status(thm)], ['65'])).
% 0.90/1.06  thf('88', plain,
% 0.90/1.06      (((v1_xboole_0 @ (sk_B @ sk_B_1)) | ((sk_E) = (sk_G)) | ((sk_E) = (sk_G)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['86', '87'])).
% 0.90/1.06  thf('89', plain, ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (sk_B @ sk_B_1)))),
% 0.90/1.06      inference('simplify', [status(thm)], ['88'])).
% 0.90/1.06  thf('90', plain,
% 0.90/1.06      (![X13 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ (sk_B @ X13))
% 0.90/1.06          | ~ (l1_pre_topc @ X13)
% 0.90/1.06          | ~ (v2_pre_topc @ X13)
% 0.90/1.06          | (v2_struct_0 @ X13))),
% 0.90/1.06      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.90/1.06  thf('91', plain,
% 0.90/1.06      ((((sk_E) = (sk_G))
% 0.90/1.06        | (v2_struct_0 @ sk_B_1)
% 0.90/1.06        | ~ (v2_pre_topc @ sk_B_1)
% 0.90/1.06        | ~ (l1_pre_topc @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['89', '90'])).
% 0.90/1.06  thf('92', plain, ((v2_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('93', plain, ((l1_pre_topc @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('94', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.90/1.06  thf('95', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('96', plain, (((sk_E) = (sk_G))),
% 0.90/1.06      inference('clc', [status(thm)], ['94', '95'])).
% 0.90/1.06  thf('97', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 0.90/1.06        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('98', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('split', [status(esa)], ['97'])).
% 0.90/1.06  thf('99', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('100', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('demod', [status(thm)], ['98', '99'])).
% 0.90/1.06  thf('101', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['96', '100'])).
% 0.90/1.06  thf('102', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['51', '101'])).
% 0.90/1.06  thf('103', plain,
% 0.90/1.06      (~
% 0.90/1.06       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) | 
% 0.90/1.06       ~
% 0.90/1.06       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.90/1.06      inference('split', [status(esa)], ['0'])).
% 0.90/1.06  thf('104', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.90/1.06      inference('split', [status(esa)], ['97'])).
% 0.90/1.06  thf('105', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('106', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.90/1.06      inference('demod', [status(thm)], ['104', '105'])).
% 0.90/1.06  thf('107', plain,
% 0.90/1.06      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.90/1.06         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 0.90/1.06      inference('sup+', [status(thm)], ['34', '50'])).
% 0.90/1.06  thf('108', plain, (((sk_E) = (sk_G))),
% 0.90/1.06      inference('clc', [status(thm)], ['94', '95'])).
% 0.90/1.06  thf('109', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('split', [status(esa)], ['0'])).
% 0.90/1.06  thf('110', plain, (((sk_D) = (sk_A))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('111', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('demod', [status(thm)], ['109', '110'])).
% 0.90/1.06  thf('112', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['108', '111'])).
% 0.90/1.06  thf('113', plain,
% 0.90/1.06      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['107', '112'])).
% 0.90/1.06  thf('114', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.90/1.06       ~
% 0.90/1.06       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.90/1.06      inference('sup-', [status(thm)], ['106', '113'])).
% 0.90/1.06  thf('115', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.90/1.06       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.90/1.06      inference('split', [status(esa)], ['97'])).
% 0.90/1.06  thf('116', plain,
% 0.90/1.06      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.90/1.06      inference('sat_resolution*', [status(thm)], ['103', '114', '115'])).
% 0.90/1.06  thf('117', plain,
% 0.90/1.06      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.06        (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)),
% 0.90/1.06      inference('simpl_trail', [status(thm)], ['102', '116'])).
% 0.90/1.06  thf('118', plain,
% 0.90/1.06      (($false)
% 0.90/1.06         <= (~
% 0.90/1.06             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.07               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.90/1.07      inference('demod', [status(thm)], ['3', '117'])).
% 0.90/1.07  thf('119', plain,
% 0.90/1.07      (~
% 0.90/1.07       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.90/1.07         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.90/1.07      inference('sat_resolution*', [status(thm)], ['103', '114'])).
% 0.90/1.07  thf('120', plain, ($false),
% 0.90/1.07      inference('simpl_trail', [status(thm)], ['118', '119'])).
% 0.90/1.07  
% 0.90/1.07  % SZS output end Refutation
% 0.90/1.07  
% 0.90/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
