%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ld2UeE2tke

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 720 expanded)
%              Number of leaves         :   39 ( 218 expanded)
%              Depth                    :   23
%              Number of atoms          : 1722 (38184 expanded)
%              Number of equality atoms :   50 ( 474 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( ( k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) @ X23 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k2_tmap_1 @ X17 @ X15 @ X18 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( X9 = X13 )
      | ~ ( r1_funct_2 @ X10 @ X11 @ X14 @ X12 @ X9 @ X13 ) ) ),
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
    inference(demod,[status(thm)],['14','15'])).

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

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_G )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B @ sk_B_1 ) )
      | ( sk_E = sk_G ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( sk_E = sk_G ) ) ),
    inference('sup-',[status(thm)],['52','76'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('79',plain,
    ( ( sk_E = sk_G )
    | ( ( sk_B @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['51','92'])).

thf('94',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('96',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 )
    = ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['34','50'])).

thf('99',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['85','86'])).

thf('100',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['88'])).

thf('107',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['94','105','106'])).

thf('108',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['93','107'])).

thf('109',plain,
    ( $false
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['94','105'])).

thf('111',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ld2UeE2tke
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 97 iterations in 0.042s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(t80_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                       ( ![F:$i]:
% 0.21/0.49                         ( ( ( v1_funct_1 @ F ) & 
% 0.21/0.49                             ( v1_funct_2 @
% 0.21/0.49                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                             ( m1_subset_1 @
% 0.21/0.49                               F @ 
% 0.21/0.49                               ( k1_zfmisc_1 @
% 0.21/0.49                                 ( k2_zfmisc_1 @
% 0.21/0.49                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                           ( ![G:$i]:
% 0.21/0.49                             ( ( ( v1_funct_1 @ G ) & 
% 0.21/0.49                                 ( v1_funct_2 @
% 0.21/0.49                                   G @ ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                   ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                                 ( m1_subset_1 @
% 0.21/0.49                                   G @ 
% 0.21/0.49                                   ( k1_zfmisc_1 @
% 0.21/0.49                                     ( k2_zfmisc_1 @
% 0.21/0.49                                       ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                               ( ( ( ( D ) = ( A ) ) & 
% 0.21/0.49                                   ( r1_funct_2 @
% 0.21/0.49                                     ( u1_struct_0 @ A ) @ 
% 0.21/0.49                                     ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                     ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.21/0.49                                 ( ( r2_funct_2 @
% 0.21/0.49                                     ( u1_struct_0 @ C ) @ 
% 0.21/0.49                                     ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.21/0.49                                   ( r2_funct_2 @
% 0.21/0.49                                     ( u1_struct_0 @ C ) @ 
% 0.21/0.49                                     ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49                ( l1_pre_topc @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                      ( ![E:$i]:
% 0.21/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                            ( v1_funct_2 @
% 0.21/0.49                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                            ( m1_subset_1 @
% 0.21/0.49                              E @ 
% 0.21/0.49                              ( k1_zfmisc_1 @
% 0.21/0.49                                ( k2_zfmisc_1 @
% 0.21/0.49                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                          ( ![F:$i]:
% 0.21/0.49                            ( ( ( v1_funct_1 @ F ) & 
% 0.21/0.49                                ( v1_funct_2 @
% 0.21/0.49                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                                ( m1_subset_1 @
% 0.21/0.49                                  F @ 
% 0.21/0.49                                  ( k1_zfmisc_1 @
% 0.21/0.49                                    ( k2_zfmisc_1 @
% 0.21/0.49                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                              ( ![G:$i]:
% 0.21/0.49                                ( ( ( v1_funct_1 @ G ) & 
% 0.21/0.49                                    ( v1_funct_2 @
% 0.21/0.49                                      G @ ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                      ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                                    ( m1_subset_1 @
% 0.21/0.49                                      G @ 
% 0.21/0.49                                      ( k1_zfmisc_1 @
% 0.21/0.49                                        ( k2_zfmisc_1 @
% 0.21/0.49                                          ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                                  ( ( ( ( D ) = ( A ) ) & 
% 0.21/0.49                                      ( r1_funct_2 @
% 0.21/0.49                                        ( u1_struct_0 @ A ) @ 
% 0.21/0.49                                        ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                        ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.21/0.49                                    ( ( r2_funct_2 @
% 0.21/0.49                                        ( u1_struct_0 @ C ) @ 
% 0.21/0.49                                        ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.21/0.49                                      ( r2_funct_2 @
% 0.21/0.49                                        ( u1_struct_0 @ C ) @ 
% 0.21/0.49                                        ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 0.21/0.49        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49             (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(t2_tsep_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(d5_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.49                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                           ( k2_partfun1 @
% 0.21/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.49                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X19)
% 0.21/0.49          | ~ (v2_pre_topc @ X19)
% 0.21/0.49          | ~ (l1_pre_topc @ X19)
% 0.21/0.49          | ~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.49          | ~ (m1_pre_topc @ X20 @ X22)
% 0.21/0.49          | ((k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19) @ 
% 0.21/0.49                 X23 @ (u1_struct_0 @ X20)))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))))
% 0.21/0.49          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))
% 0.21/0.49          | ~ (v1_funct_1 @ X23)
% 0.21/0.49          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | (v2_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.49               (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13', '16', '17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '19'])).
% 0.21/0.49  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '23', '24', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49        | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '29'])).
% 0.21/0.49  thf('31', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_D)
% 0.21/0.49        | ((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.49      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E)
% 0.21/0.49         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(d4_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                 ( m1_subset_1 @
% 0.21/0.49                   C @ 
% 0.21/0.49                   ( k1_zfmisc_1 @
% 0.21/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.49                     ( k2_partfun1 @
% 0.21/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X15)
% 0.21/0.49          | ~ (v2_pre_topc @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X15)
% 0.21/0.49          | ~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.49          | ((k2_tmap_1 @ X17 @ X15 @ X18 @ X16)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 0.21/0.49                 X18 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.21/0.49          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.21/0.49          | ~ (v1_funct_1 @ X18)
% 0.21/0.49          | ~ (l1_pre_topc @ X17)
% 0.21/0.49          | ~ (v2_pre_topc @ X17)
% 0.21/0.49          | (v2_struct_0 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.49               (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ X0)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['38', '39', '40', '41', '42', '43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49        | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '45'])).
% 0.21/0.49  thf('47', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_D)
% 0.21/0.49        | ((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.49      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.21/0.49         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49            sk_E @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.21/0.49         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '50'])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ sk_G)),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(redefinition_r1_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.49         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.21/0.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.49       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.49          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | (v1_xboole_0 @ X12)
% 0.21/0.49          | (v1_xboole_0 @ X11)
% 0.21/0.49          | ~ (v1_funct_1 @ X13)
% 0.21/0.49          | ~ (v1_funct_2 @ X13 @ X14 @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.21/0.49          | ((X9) = (X13))
% 0.21/0.49          | ~ (r1_funct_2 @ X10 @ X11 @ X14 @ X12 @ X9 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.21/0.49             X1 @ sk_E @ X0)
% 0.21/0.49          | ((sk_E) = (X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.49               (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ X2 @ 
% 0.21/0.49             X1 @ sk_E @ X0)
% 0.21/0.49          | ((sk_E) = (X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_G)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | ~ (m1_subset_1 @ sk_G @ 
% 0.21/0.49             (k1_zfmisc_1 @ 
% 0.21/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.49        | ((sk_E) = (sk_G)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '61'])).
% 0.21/0.49  thf('63', plain, ((v1_funct_1 @ sk_G)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_G @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | ((sk_E) = (sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.49  thf(rc7_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ?[B:$i]:
% 0.21/0.49         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.49          | ~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (v2_pre_topc @ X8)
% 0.21/0.49          | (v2_struct_0 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.49  thf(t5_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.49          | ~ (v1_xboole_0 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (sk_B @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_E) = (sk_G))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (sk_B @ sk_B_1))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '70'])).
% 0.21/0.49  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('73', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_E) = (sk_G))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (sk_B @ sk_B_1))
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.49  thf('75', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ (sk_B @ sk_B_1)) | ((sk_E) = (sk_G)))),
% 0.21/0.49      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (![X0 : $i]: ((r1_tarski @ (sk_B @ sk_B_1) @ X0) | ((sk_E) = (sk_G)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '76'])).
% 0.21/0.49  thf(t3_xboole_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.49  thf('79', plain, ((((sk_E) = (sk_G)) | ((sk_B @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (sk_B @ X8))
% 0.21/0.49          | ~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (v2_pre_topc @ X8)
% 0.21/0.49          | (v2_struct_0 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.49        | ((sk_E) = (sk_G))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.49  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.49  thf('83', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('85', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.21/0.49  thf('86', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('87', plain, (((sk_E) = (sk_G))),
% 0.21/0.49      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.49  thf('88', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)
% 0.21/0.49        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('89', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['88'])).
% 0.21/0.49  thf('90', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['87', '91'])).
% 0.21/0.49  thf('93', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['51', '92'])).
% 0.21/0.49  thf('94', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)) | 
% 0.21/0.49       ~
% 0.21/0.49       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('95', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['88'])).
% 0.21/0.49  thf('96', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('97', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['95', '96'])).
% 0.21/0.49  thf('98', plain,
% 0.21/0.49      (((k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1)
% 0.21/0.49         = (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '50'])).
% 0.21/0.49  thf('99', plain, (((sk_E) = (sk_G))),
% 0.21/0.49      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.49  thf('100', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('101', plain, (((sk_D) = (sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('102', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.49  thf('103', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k3_tmap_1 @ sk_D @ sk_B_1 @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['99', '102'])).
% 0.21/0.49  thf('104', plain,
% 0.21/0.49      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49               (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['98', '103'])).
% 0.21/0.49  thf('105', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.21/0.49       ~
% 0.21/0.49       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['97', '104'])).
% 0.21/0.49  thf('106', plain,
% 0.21/0.49      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.21/0.49       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.21/0.50      inference('split', [status(esa)], ['88'])).
% 0.21/0.50  thf('107', plain,
% 0.21/0.50      (((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50         (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['94', '105', '106'])).
% 0.21/0.50  thf('108', plain,
% 0.21/0.50      ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50        (k2_tmap_1 @ sk_D @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['93', '107'])).
% 0.21/0.50  thf('109', plain,
% 0.21/0.50      (($false)
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50               (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F)))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '108'])).
% 0.21/0.50  thf('110', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50         (k2_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ sk_C_1) @ sk_F))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['94', '105'])).
% 0.21/0.50  thf('111', plain, ($false),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
