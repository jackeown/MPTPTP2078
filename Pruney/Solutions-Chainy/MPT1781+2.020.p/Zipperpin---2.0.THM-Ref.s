%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZqO8LZcdDx

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:44 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  348 (5306 expanded)
%              Number of leaves         :   35 (1504 expanded)
%              Depth                    :   44
%              Number of atoms          : 5865 (163039 expanded)
%              Number of equality atoms :   43 (2637 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('17',plain,(
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

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf(t73_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                   => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                      = ( k1_funct_1 @ F @ G ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30 ) @ X29 )
      | ( m1_subset_1 @ ( sk_G @ X29 @ X30 @ X26 @ X28 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_tmap_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_G @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_G @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','51','69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('75',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( X6 = X9 )
      | ~ ( r2_funct_2 @ X7 @ X8 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('82',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('83',plain,
    ( ( sk_C
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) @ X32 @ ( k3_tmap_1 @ X34 @ X31 @ X33 @ X33 @ X32 ) )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','101'])).

thf('103',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','101'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('116',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','113','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('126',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('136',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) @ X32 @ ( k3_tmap_1 @ X34 @ X31 @ X33 @ X33 @ X32 ) )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('139',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('153',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( X6 = X9 )
      | ~ ( r2_funct_2 @ X7 @ X8 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('156',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k4_tmap_1 @ sk_A @ sk_B )
      = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('162',plain,(
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

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('165',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','175'])).

thf('177',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('180',plain,(
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

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('183',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['178','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','193'])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('198',plain,(
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

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('201',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('202',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['195','211'])).

thf('213',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','176','194','212'])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','132','133','213'])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['214'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('216',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('225',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('226',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('227',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30 ) @ X29 )
      | ( r2_hidden @ ( sk_G @ X29 @ X30 @ X26 @ X28 @ X25 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_tmap_1])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_G @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('230',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_G @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['228','229','230','231','232'])).

thf('234',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','101'])).

thf('235',plain,
    ( sk_C
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['83','101'])).

thf('236',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_G @ sk_C @ X1 @ X2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1 ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['225','236'])).

thf('238',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('239',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['224','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['223','244'])).

thf('246',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','176','194','212'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ ( u1_struct_0 @ sk_B ) )
      | ( X41
        = ( k1_funct_1 @ sk_C @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['222','252'])).

thf('254',plain,
    ( ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['221'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['249'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('257',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( r2_hidden @ X40 @ ( u1_struct_0 @ X38 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X39 @ X38 ) @ X40 )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
        = ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
        = ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['255','259'])).

thf('261',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['214'])).

thf('267',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('268',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ X3 )
      | ( ( k3_funct_2 @ X3 @ X4 @ X2 @ X5 )
        = ( k1_funct_1 @ X2 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('271',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['266','272'])).

thf('274',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30 ) @ X29 )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) @ X30 @ ( sk_G @ X29 @ X30 @ X26 @ X28 @ X25 ) )
       != ( k1_funct_1 @ X29 @ ( sk_G @ X29 @ X30 @ X26 @ X28 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_tmap_1])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('277',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('278',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('279',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['275','276','277','278','279','280','281','282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_C @ ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
       != ( sk_G @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','289'])).

thf('291',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','292'])).

thf('294',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','176','194','212'])).

thf('295',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['293','294','295','296'])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['300','301'])).

thf('303',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['302','303'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('305',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('306',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('308',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('309',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['306','309'])).

thf('311',plain,(
    $false ),
    inference(demod,[status(thm)],['0','310'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZqO8LZcdDx
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:08:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.52/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.52/1.74  % Solved by: fo/fo7.sh
% 1.52/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.74  % done 1376 iterations in 1.284s
% 1.52/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.52/1.74  % SZS output start Refutation
% 1.52/1.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.52/1.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.52/1.74  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.52/1.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.52/1.74  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.52/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.74  thf(sk_C_type, type, sk_C: $i).
% 1.52/1.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.52/1.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.52/1.74  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 1.52/1.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.52/1.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.52/1.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.52/1.74  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.52/1.74  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.52/1.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.52/1.74  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.74  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.52/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.52/1.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.52/1.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.74  thf(t96_tmap_1, conjecture,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.52/1.74           ( ![C:$i]:
% 1.52/1.74             ( ( ( v1_funct_1 @ C ) & 
% 1.52/1.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.52/1.74                 ( m1_subset_1 @
% 1.52/1.74                   C @ 
% 1.52/1.74                   ( k1_zfmisc_1 @
% 1.52/1.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.52/1.74               ( ( ![D:$i]:
% 1.52/1.74                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.52/1.74                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.52/1.74                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.52/1.74                 ( r2_funct_2 @
% 1.52/1.74                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.74                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.52/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.74    (~( ![A:$i]:
% 1.52/1.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.52/1.74            ( l1_pre_topc @ A ) ) =>
% 1.52/1.74          ( ![B:$i]:
% 1.52/1.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.52/1.74              ( ![C:$i]:
% 1.52/1.74                ( ( ( v1_funct_1 @ C ) & 
% 1.52/1.74                    ( v1_funct_2 @
% 1.52/1.74                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.52/1.74                    ( m1_subset_1 @
% 1.52/1.74                      C @ 
% 1.52/1.74                      ( k1_zfmisc_1 @
% 1.52/1.74                        ( k2_zfmisc_1 @
% 1.52/1.74                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.52/1.74                  ( ( ![D:$i]:
% 1.52/1.74                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.52/1.74                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.52/1.74                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.52/1.74                    ( r2_funct_2 @
% 1.52/1.74                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.52/1.74                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.52/1.74    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.52/1.74  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(t2_tsep_1, axiom,
% 1.52/1.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.52/1.74  thf('2', plain,
% 1.52/1.74      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.52/1.74  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('5', plain,
% 1.52/1.74      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.52/1.74  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(dt_k4_tmap_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.52/1.74         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.52/1.74       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.52/1.74         ( v1_funct_2 @
% 1.52/1.74           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.52/1.74         ( m1_subset_1 @
% 1.52/1.74           ( k4_tmap_1 @ A @ B ) @ 
% 1.52/1.74           ( k1_zfmisc_1 @
% 1.52/1.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.52/1.74  thf('7', plain,
% 1.52/1.74      (![X22 : $i, X23 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X22)
% 1.52/1.74          | ~ (v2_pre_topc @ X22)
% 1.52/1.74          | (v2_struct_0 @ X22)
% 1.52/1.74          | ~ (m1_pre_topc @ X23 @ X22)
% 1.52/1.74          | (m1_subset_1 @ (k4_tmap_1 @ X22 @ X23) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22)))))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.52/1.74  thf('8', plain,
% 1.52/1.74      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74         (k1_zfmisc_1 @ 
% 1.52/1.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['6', '7'])).
% 1.52/1.74  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('11', plain,
% 1.52/1.74      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74         (k1_zfmisc_1 @ 
% 1.52/1.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.52/1.74  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('13', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('16', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(dt_k3_tmap_1, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.52/1.74         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.52/1.74         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.52/1.74         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.52/1.74         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.74         ( m1_subset_1 @
% 1.52/1.74           E @ 
% 1.52/1.74           ( k1_zfmisc_1 @
% 1.52/1.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.74       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.52/1.74         ( v1_funct_2 @
% 1.52/1.74           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.52/1.74           ( u1_struct_0 @ B ) ) & 
% 1.52/1.74         ( m1_subset_1 @
% 1.52/1.74           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.52/1.74           ( k1_zfmisc_1 @
% 1.52/1.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.52/1.74  thf('17', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('18', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['16', '17'])).
% 1.52/1.74  thf('19', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('23', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.52/1.74  thf('24', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['15', '23'])).
% 1.52/1.74  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('27', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.52/1.74  thf('28', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['27'])).
% 1.52/1.74  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('30', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('clc', [status(thm)], ['28', '29'])).
% 1.52/1.74  thf('31', plain,
% 1.52/1.74      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['14', '30'])).
% 1.52/1.74  thf(t73_tmap_1, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.52/1.74             ( l1_pre_topc @ B ) ) =>
% 1.52/1.74           ( ![C:$i]:
% 1.52/1.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.52/1.74               ( ![D:$i]:
% 1.52/1.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.52/1.74                   ( ![E:$i]:
% 1.52/1.74                     ( ( ( v1_funct_1 @ E ) & 
% 1.52/1.74                         ( v1_funct_2 @
% 1.52/1.74                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.74                         ( m1_subset_1 @
% 1.52/1.74                           E @ 
% 1.52/1.74                           ( k1_zfmisc_1 @
% 1.52/1.74                             ( k2_zfmisc_1 @
% 1.52/1.74                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.74                       ( ( m1_pre_topc @ C @ D ) =>
% 1.52/1.74                         ( ![F:$i]:
% 1.52/1.74                           ( ( ( v1_funct_1 @ F ) & 
% 1.52/1.74                               ( v1_funct_2 @
% 1.52/1.74                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.74                               ( m1_subset_1 @
% 1.52/1.74                                 F @ 
% 1.52/1.74                                 ( k1_zfmisc_1 @
% 1.52/1.74                                   ( k2_zfmisc_1 @
% 1.52/1.74                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.74                             ( ( ![G:$i]:
% 1.52/1.74                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 1.52/1.74                                   ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 1.52/1.74                                     ( ( k3_funct_2 @
% 1.52/1.74                                         ( u1_struct_0 @ D ) @ 
% 1.52/1.74                                         ( u1_struct_0 @ B ) @ E @ G ) =
% 1.52/1.74                                       ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 1.52/1.74                               ( r2_funct_2 @
% 1.52/1.74                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.52/1.74                                 ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.52/1.74  thf('32', plain,
% 1.52/1.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X25)
% 1.52/1.74          | ~ (v2_pre_topc @ X25)
% 1.52/1.74          | ~ (l1_pre_topc @ X25)
% 1.52/1.74          | (v2_struct_0 @ X26)
% 1.52/1.74          | ~ (m1_pre_topc @ X26 @ X27)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X26)
% 1.52/1.74          | ~ (v1_funct_1 @ X29)
% 1.52/1.74          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (m1_subset_1 @ X29 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 1.52/1.74             (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30) @ X29)
% 1.52/1.74          | (m1_subset_1 @ (sk_G @ X29 @ X30 @ X26 @ X28 @ X25) @ 
% 1.52/1.74             (u1_struct_0 @ X26))
% 1.52/1.74          | ~ (m1_subset_1 @ X30 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (v1_funct_1 @ X30)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X27)
% 1.52/1.74          | (v2_struct_0 @ X28)
% 1.52/1.74          | ~ (l1_pre_topc @ X27)
% 1.52/1.74          | ~ (v2_pre_topc @ X27)
% 1.52/1.74          | (v2_struct_0 @ X27))),
% 1.52/1.74      inference('cnf', [status(esa)], [t73_tmap_1])).
% 1.52/1.74  thf('33', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X1 @ 
% 1.52/1.74              X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ X2))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['31', '32'])).
% 1.52/1.74  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('36', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('37', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 1.52/1.74             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('38', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['36', '37'])).
% 1.52/1.74  thf('39', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('43', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.52/1.74  thf('44', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['35', '43'])).
% 1.52/1.74  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('47', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.52/1.74  thf('48', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['47'])).
% 1.52/1.74  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('50', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('clc', [status(thm)], ['48', '49'])).
% 1.52/1.74  thf('51', plain,
% 1.52/1.74      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['34', '50'])).
% 1.52/1.74  thf('52', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('54', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('55', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('56', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['54', '55'])).
% 1.52/1.74  thf('57', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('61', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 1.52/1.74  thf('62', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['53', '61'])).
% 1.52/1.74  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('65', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.52/1.74      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.52/1.74  thf('66', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['65'])).
% 1.52/1.74  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('68', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 1.52/1.74      inference('clc', [status(thm)], ['66', '67'])).
% 1.52/1.74  thf('69', plain,
% 1.52/1.74      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('sup-', [status(thm)], ['52', '68'])).
% 1.52/1.74  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('72', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X1 @ 
% 1.52/1.74              X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ X2))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['33', '51', '69', '70', '71'])).
% 1.52/1.74  thf('73', plain,
% 1.52/1.74      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['14', '30'])).
% 1.52/1.74  thf('74', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(redefinition_r2_funct_2, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.52/1.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.52/1.74         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.52/1.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.74       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.52/1.74  thf('75', plain,
% 1.52/1.74      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.52/1.74         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.52/1.74          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 1.52/1.74          | ~ (v1_funct_1 @ X6)
% 1.52/1.74          | ~ (v1_funct_1 @ X9)
% 1.52/1.74          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 1.52/1.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.52/1.74          | ((X6) = (X9))
% 1.52/1.74          | ~ (r2_funct_2 @ X7 @ X8 @ X6 @ X9))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.52/1.74  thf('76', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             X0)
% 1.52/1.74          | ((sk_C) = (X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['74', '75'])).
% 1.52/1.74  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('78', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('79', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             X0)
% 1.52/1.74          | ((sk_C) = (X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.52/1.74  thf('80', plain,
% 1.52/1.74      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74        | ((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['73', '79'])).
% 1.52/1.74  thf('81', plain,
% 1.52/1.74      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('sup-', [status(thm)], ['52', '68'])).
% 1.52/1.74  thf('82', plain,
% 1.52/1.74      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['34', '50'])).
% 1.52/1.74  thf('83', plain,
% 1.52/1.74      ((((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.52/1.74      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.52/1.74  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('85', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(t74_tmap_1, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.52/1.74             ( l1_pre_topc @ B ) ) =>
% 1.52/1.74           ( ![C:$i]:
% 1.52/1.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.52/1.74               ( ![D:$i]:
% 1.52/1.74                 ( ( ( v1_funct_1 @ D ) & 
% 1.52/1.74                     ( v1_funct_2 @
% 1.52/1.74                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.52/1.74                     ( m1_subset_1 @
% 1.52/1.74                       D @ 
% 1.52/1.74                       ( k1_zfmisc_1 @
% 1.52/1.74                         ( k2_zfmisc_1 @
% 1.52/1.74                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.52/1.74                   ( r2_funct_2 @
% 1.52/1.74                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 1.52/1.74                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.52/1.74  thf('86', plain,
% 1.52/1.74      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X31)
% 1.52/1.74          | ~ (v2_pre_topc @ X31)
% 1.52/1.74          | ~ (l1_pre_topc @ X31)
% 1.52/1.74          | ~ (v1_funct_1 @ X32)
% 1.52/1.74          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 1.52/1.74          | ~ (m1_subset_1 @ X32 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31) @ X32 @ 
% 1.52/1.74             (k3_tmap_1 @ X34 @ X31 @ X33 @ X33 @ X32))
% 1.52/1.74          | ~ (m1_pre_topc @ X33 @ X34)
% 1.52/1.74          | (v2_struct_0 @ X33)
% 1.52/1.74          | ~ (l1_pre_topc @ X34)
% 1.52/1.74          | ~ (v2_pre_topc @ X34)
% 1.52/1.74          | (v2_struct_0 @ X34))),
% 1.52/1.74      inference('cnf', [status(esa)], [t74_tmap_1])).
% 1.52/1.74  thf('87', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['85', '86'])).
% 1.52/1.74  thf('88', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('92', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 1.52/1.74  thf('93', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['84', '92'])).
% 1.52/1.74  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('96', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.52/1.74  thf('97', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['96'])).
% 1.52/1.74  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('99', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 1.52/1.74      inference('clc', [status(thm)], ['97', '98'])).
% 1.52/1.74  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('101', plain,
% 1.52/1.74      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.52/1.74        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('clc', [status(thm)], ['99', '100'])).
% 1.52/1.74  thf('102', plain,
% 1.52/1.74      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('demod', [status(thm)], ['83', '101'])).
% 1.52/1.74  thf('103', plain,
% 1.52/1.74      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('demod', [status(thm)], ['83', '101'])).
% 1.52/1.74  thf('104', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (m1_subset_1 @ (sk_G @ sk_C @ X1 @ X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ X2))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['72', '102', '103'])).
% 1.52/1.74  thf('105', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['13', '104'])).
% 1.52/1.74  thf('106', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('107', plain,
% 1.52/1.74      (![X22 : $i, X23 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X22)
% 1.52/1.74          | ~ (v2_pre_topc @ X22)
% 1.52/1.74          | (v2_struct_0 @ X22)
% 1.52/1.74          | ~ (m1_pre_topc @ X23 @ X22)
% 1.52/1.74          | (v1_funct_2 @ (k4_tmap_1 @ X22 @ X23) @ (u1_struct_0 @ X23) @ 
% 1.52/1.74             (u1_struct_0 @ X22)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.52/1.74  thf('108', plain,
% 1.52/1.74      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74         (u1_struct_0 @ sk_A))
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['106', '107'])).
% 1.52/1.74  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('111', plain,
% 1.52/1.74      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74         (u1_struct_0 @ sk_A))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.52/1.74  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('113', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('114', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('115', plain,
% 1.52/1.74      (![X22 : $i, X23 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X22)
% 1.52/1.74          | ~ (v2_pre_topc @ X22)
% 1.52/1.74          | (v2_struct_0 @ X22)
% 1.52/1.74          | ~ (m1_pre_topc @ X23 @ X22)
% 1.52/1.74          | (v1_funct_1 @ (k4_tmap_1 @ X22 @ X23)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.52/1.74  thf('116', plain,
% 1.52/1.74      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['114', '115'])).
% 1.52/1.74  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('119', plain,
% 1.52/1.74      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['116', '117', '118'])).
% 1.52/1.74  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('121', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('122', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['105', '113', '121'])).
% 1.52/1.74  thf('123', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['122'])).
% 1.52/1.74  thf('124', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['5', '123'])).
% 1.52/1.74  thf('125', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(dt_m1_pre_topc, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( l1_pre_topc @ A ) =>
% 1.52/1.74       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.52/1.74  thf('126', plain,
% 1.52/1.74      (![X11 : $i, X12 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X11 @ X12)
% 1.52/1.74          | (l1_pre_topc @ X11)
% 1.52/1.74          | ~ (l1_pre_topc @ X12))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.52/1.74  thf('127', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.52/1.74      inference('sup-', [status(thm)], ['125', '126'])).
% 1.52/1.74  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('129', plain, ((l1_pre_topc @ sk_B)),
% 1.52/1.74      inference('demod', [status(thm)], ['127', '128'])).
% 1.52/1.74  thf('130', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['124', '129'])).
% 1.52/1.74  thf('131', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['4', '130'])).
% 1.52/1.74  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('134', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('135', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('136', plain,
% 1.52/1.74      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X31)
% 1.52/1.74          | ~ (v2_pre_topc @ X31)
% 1.52/1.74          | ~ (l1_pre_topc @ X31)
% 1.52/1.74          | ~ (v1_funct_1 @ X32)
% 1.52/1.74          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 1.52/1.74          | ~ (m1_subset_1 @ X32 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31) @ X32 @ 
% 1.52/1.74             (k3_tmap_1 @ X34 @ X31 @ X33 @ X33 @ X32))
% 1.52/1.74          | ~ (m1_pre_topc @ X33 @ X34)
% 1.52/1.74          | (v2_struct_0 @ X33)
% 1.52/1.74          | ~ (l1_pre_topc @ X34)
% 1.52/1.74          | ~ (v2_pre_topc @ X34)
% 1.52/1.74          | (v2_struct_0 @ X34))),
% 1.52/1.74      inference('cnf', [status(esa)], [t74_tmap_1])).
% 1.52/1.74  thf('137', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['135', '136'])).
% 1.52/1.74  thf('138', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('139', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('142', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 1.52/1.74  thf('143', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['134', '142'])).
% 1.52/1.74  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('146', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['143', '144', '145'])).
% 1.52/1.74  thf('147', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['146'])).
% 1.52/1.74  thf('148', plain, (~ (v2_struct_0 @ sk_B)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('149', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 1.52/1.74      inference('clc', [status(thm)], ['147', '148'])).
% 1.52/1.74  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('151', plain,
% 1.52/1.74      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74        (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.52/1.74      inference('clc', [status(thm)], ['149', '150'])).
% 1.52/1.74  thf('152', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('153', plain,
% 1.52/1.74      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.52/1.74         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.52/1.74          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 1.52/1.74          | ~ (v1_funct_1 @ X6)
% 1.52/1.74          | ~ (v1_funct_1 @ X9)
% 1.52/1.74          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 1.52/1.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.52/1.74          | ((X6) = (X9))
% 1.52/1.74          | ~ (r2_funct_2 @ X7 @ X8 @ X6 @ X9))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.52/1.74  thf('154', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 1.52/1.74          | ((k4_tmap_1 @ sk_A @ sk_B) = (X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['152', '153'])).
% 1.52/1.74  thf('155', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('156', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('157', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 1.52/1.74          | ((k4_tmap_1 @ sk_A @ sk_B) = (X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['154', '155', '156'])).
% 1.52/1.74  thf('158', plain,
% 1.52/1.74      ((~ (v1_funct_1 @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74        | ~ (v1_funct_2 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74        | ~ (m1_subset_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74        | ((k4_tmap_1 @ sk_A @ sk_B)
% 1.52/1.74            = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ 
% 1.52/1.74               (k4_tmap_1 @ sk_A @ sk_B))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['151', '157'])).
% 1.52/1.74  thf('159', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('160', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('161', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('162', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('163', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_1 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['161', '162'])).
% 1.52/1.74  thf('164', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('165', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('168', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_1 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 1.52/1.74  thf('169', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['160', '168'])).
% 1.52/1.74  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('172', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 1.52/1.74      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.52/1.74  thf('173', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_funct_1 @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['172'])).
% 1.52/1.74  thf('174', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('175', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v1_funct_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 1.52/1.74      inference('clc', [status(thm)], ['173', '174'])).
% 1.52/1.74  thf('176', plain,
% 1.52/1.74      ((v1_funct_1 @ 
% 1.52/1.74        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['159', '175'])).
% 1.52/1.74  thf('177', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('178', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('179', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('180', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 1.52/1.74             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('181', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_2 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['179', '180'])).
% 1.52/1.74  thf('182', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('183', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('186', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_funct_2 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 1.52/1.74  thf('187', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['178', '186'])).
% 1.52/1.74  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('189', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('190', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('demod', [status(thm)], ['187', '188', '189'])).
% 1.52/1.74  thf('191', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_funct_2 @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['190'])).
% 1.52/1.74  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('193', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v1_funct_2 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('clc', [status(thm)], ['191', '192'])).
% 1.52/1.74  thf('194', plain,
% 1.52/1.74      ((v1_funct_2 @ 
% 1.52/1.74        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['177', '193'])).
% 1.52/1.74  thf('195', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('196', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('197', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('198', plain,
% 1.52/1.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X17 @ X18)
% 1.52/1.74          | ~ (m1_pre_topc @ X19 @ X18)
% 1.52/1.74          | ~ (l1_pre_topc @ X20)
% 1.52/1.74          | ~ (v2_pre_topc @ X20)
% 1.52/1.74          | (v2_struct_0 @ X20)
% 1.52/1.74          | ~ (l1_pre_topc @ X18)
% 1.52/1.74          | ~ (v2_pre_topc @ X18)
% 1.52/1.74          | (v2_struct_0 @ X18)
% 1.52/1.74          | ~ (v1_funct_1 @ X21)
% 1.52/1.74          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 1.52/1.74          | ~ (m1_subset_1 @ X21 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 1.52/1.74          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.52/1.74  thf('199', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((m1_subset_1 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['197', '198'])).
% 1.52/1.74  thf('200', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('201', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('202', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('204', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((m1_subset_1 @ 
% 1.52/1.74           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (v2_struct_0 @ X1)
% 1.52/1.74          | ~ (v2_pre_topc @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X1)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.52/1.74      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 1.52/1.74  thf('205', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['196', '204'])).
% 1.52/1.74  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('208', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('demod', [status(thm)], ['205', '206', '207'])).
% 1.52/1.74  thf('209', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((m1_subset_1 @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           (k1_zfmisc_1 @ 
% 1.52/1.74            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['208'])).
% 1.52/1.74  thf('210', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('211', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             (k1_zfmisc_1 @ 
% 1.52/1.74              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('clc', [status(thm)], ['209', '210'])).
% 1.52/1.74  thf('212', plain,
% 1.52/1.74      ((m1_subset_1 @ 
% 1.52/1.74        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['195', '211'])).
% 1.52/1.74  thf('213', plain,
% 1.52/1.74      (((k4_tmap_1 @ sk_A @ sk_B)
% 1.52/1.74         = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.52/1.74      inference('demod', [status(thm)], ['158', '176', '194', '212'])).
% 1.52/1.74  thf('214', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['131', '132', '133', '213'])).
% 1.52/1.74  thf('215', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['214'])).
% 1.52/1.74  thf(t55_pre_topc, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.52/1.74           ( ![C:$i]:
% 1.52/1.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.52/1.74               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.52/1.74  thf('216', plain,
% 1.52/1.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X14)
% 1.52/1.74          | ~ (m1_pre_topc @ X14 @ X15)
% 1.52/1.74          | (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 1.52/1.74          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.52/1.74          | ~ (l1_pre_topc @ X15)
% 1.52/1.74          | (v2_struct_0 @ X15))),
% 1.52/1.74      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.52/1.74  thf('217', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ X0))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B))),
% 1.52/1.74      inference('sup-', [status(thm)], ['215', '216'])).
% 1.52/1.74  thf('218', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ X0))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['217'])).
% 1.52/1.74  thf('219', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['3', '218'])).
% 1.52/1.74  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('221', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('demod', [status(thm)], ['219', '220'])).
% 1.52/1.74  thf('222', plain,
% 1.52/1.74      (((m1_subset_1 @ 
% 1.52/1.74         (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74         (u1_struct_0 @ sk_A))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['221'])).
% 1.52/1.74  thf('223', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('224', plain,
% 1.52/1.74      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.52/1.74  thf('225', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('226', plain,
% 1.52/1.74      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['14', '30'])).
% 1.52/1.74  thf('227', plain,
% 1.52/1.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X25)
% 1.52/1.74          | ~ (v2_pre_topc @ X25)
% 1.52/1.74          | ~ (l1_pre_topc @ X25)
% 1.52/1.74          | (v2_struct_0 @ X26)
% 1.52/1.74          | ~ (m1_pre_topc @ X26 @ X27)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X26)
% 1.52/1.74          | ~ (v1_funct_1 @ X29)
% 1.52/1.74          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (m1_subset_1 @ X29 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 1.52/1.74             (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30) @ X29)
% 1.52/1.74          | (r2_hidden @ (sk_G @ X29 @ X30 @ X26 @ X28 @ X25) @ 
% 1.52/1.74             (u1_struct_0 @ X28))
% 1.52/1.74          | ~ (m1_subset_1 @ X30 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (v1_funct_1 @ X30)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X27)
% 1.52/1.74          | (v2_struct_0 @ X28)
% 1.52/1.74          | ~ (l1_pre_topc @ X27)
% 1.52/1.74          | ~ (v2_pre_topc @ X27)
% 1.52/1.74          | (v2_struct_0 @ X27))),
% 1.52/1.74      inference('cnf', [status(esa)], [t73_tmap_1])).
% 1.52/1.74  thf('228', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X1 @ 
% 1.52/1.74              X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['226', '227'])).
% 1.52/1.74  thf('229', plain,
% 1.52/1.74      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 1.52/1.74        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['34', '50'])).
% 1.52/1.74  thf('230', plain,
% 1.52/1.74      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('sup-', [status(thm)], ['52', '68'])).
% 1.52/1.74  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('232', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('233', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X1 @ 
% 1.52/1.74              X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ 
% 1.52/1.74             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['228', '229', '230', '231', '232'])).
% 1.52/1.74  thf('234', plain,
% 1.52/1.74      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('demod', [status(thm)], ['83', '101'])).
% 1.52/1.74  thf('235', plain,
% 1.52/1.74      (((sk_C) = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 1.52/1.74      inference('demod', [status(thm)], ['83', '101'])).
% 1.52/1.74  thf('236', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ X1 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (r2_hidden @ (sk_G @ sk_C @ X1 @ X2 @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ X2 @ sk_B @ X1) @ sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X2)
% 1.52/1.74          | ~ (m1_pre_topc @ X2 @ X0)
% 1.52/1.74          | (v2_struct_0 @ X2)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['233', '234', '235'])).
% 1.52/1.74  thf('237', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['225', '236'])).
% 1.52/1.74  thf('238', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('239', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('240', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['237', '238', '239'])).
% 1.52/1.74  thf('241', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['240'])).
% 1.52/1.74  thf('242', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['224', '241'])).
% 1.52/1.74  thf('243', plain, ((l1_pre_topc @ sk_B)),
% 1.52/1.74      inference('demod', [status(thm)], ['127', '128'])).
% 1.52/1.74  thf('244', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | (r2_hidden @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['242', '243'])).
% 1.52/1.74  thf('245', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | (r2_hidden @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74           sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['223', '244'])).
% 1.52/1.74  thf('246', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('247', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('248', plain,
% 1.52/1.74      (((k4_tmap_1 @ sk_A @ sk_B)
% 1.52/1.74         = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.52/1.74      inference('demod', [status(thm)], ['158', '176', '194', '212'])).
% 1.52/1.74  thf('249', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_hidden @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 1.52/1.74  thf('250', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (r2_hidden @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['249'])).
% 1.52/1.74  thf('251', plain,
% 1.52/1.74      (![X41 : $i]:
% 1.52/1.74         (~ (r2_hidden @ X41 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | ((X41) = (k1_funct_1 @ sk_C @ X41))
% 1.52/1.74          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('252', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | ~ (m1_subset_1 @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74             (u1_struct_0 @ sk_A))
% 1.52/1.74        | ((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.74            = (k1_funct_1 @ sk_C @ 
% 1.52/1.74               (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['250', '251'])).
% 1.52/1.74  thf('253', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | ((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.74            = (k1_funct_1 @ sk_C @ 
% 1.52/1.74               (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['222', '252'])).
% 1.52/1.74  thf('254', plain,
% 1.52/1.74      ((((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.74          = (k1_funct_1 @ sk_C @ 
% 1.52/1.74             (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['253'])).
% 1.52/1.74  thf('255', plain,
% 1.52/1.74      (((m1_subset_1 @ 
% 1.52/1.74         (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74         (u1_struct_0 @ sk_A))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['221'])).
% 1.52/1.74  thf('256', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (r2_hidden @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['249'])).
% 1.52/1.74  thf(t95_tmap_1, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.52/1.74           ( ![C:$i]:
% 1.52/1.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.52/1.74               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.52/1.74                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.52/1.74  thf('257', plain,
% 1.52/1.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X38)
% 1.52/1.74          | ~ (m1_pre_topc @ X38 @ X39)
% 1.52/1.74          | ~ (r2_hidden @ X40 @ (u1_struct_0 @ X38))
% 1.52/1.74          | ((k1_funct_1 @ (k4_tmap_1 @ X39 @ X38) @ X40) = (X40))
% 1.52/1.74          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 1.52/1.74          | ~ (l1_pre_topc @ X39)
% 1.52/1.74          | ~ (v2_pre_topc @ X39)
% 1.52/1.74          | (v2_struct_0 @ X39))),
% 1.52/1.74      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.52/1.74  thf('258', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v2_struct_0 @ sk_A)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (m1_subset_1 @ 
% 1.52/1.74               (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74               (u1_struct_0 @ X0))
% 1.52/1.74          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.52/1.74              (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74              = (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B))),
% 1.52/1.74      inference('sup-', [status(thm)], ['256', '257'])).
% 1.52/1.74  thf('259', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.52/1.74              (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74              = (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ 
% 1.52/1.74               (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74               (u1_struct_0 @ X0))
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['258'])).
% 1.52/1.74  thf('260', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74            (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74            = (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['255', '259'])).
% 1.52/1.74  thf('261', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('262', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('263', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('264', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v2_struct_0 @ sk_A)
% 1.52/1.74        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74            (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74            = (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))),
% 1.52/1.74      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 1.52/1.74  thf('265', plain,
% 1.52/1.74      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74          (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74          = (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['264'])).
% 1.52/1.74  thf('266', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_B)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (m1_subset_1 @ 
% 1.52/1.74           (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 1.52/1.74           (u1_struct_0 @ sk_B))
% 1.52/1.74        | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('simplify', [status(thm)], ['214'])).
% 1.52/1.74  thf('267', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf(redefinition_k3_funct_2, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.52/1.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.52/1.74         ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.52/1.74         ( m1_subset_1 @ D @ A ) ) =>
% 1.52/1.74       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.52/1.74  thf('268', plain,
% 1.52/1.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.52/1.74         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 1.52/1.74          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 1.52/1.74          | ~ (v1_funct_1 @ X2)
% 1.52/1.74          | (v1_xboole_0 @ X3)
% 1.52/1.74          | ~ (m1_subset_1 @ X5 @ X3)
% 1.52/1.74          | ((k3_funct_2 @ X3 @ X4 @ X2 @ X5) = (k1_funct_1 @ X2 @ X5)))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.52/1.74  thf('269', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74            (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 1.52/1.74            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['267', '268'])).
% 1.52/1.74  thf('270', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('271', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('272', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74            (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 1.52/1.74            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0))
% 1.52/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.52/1.74      inference('demod', [status(thm)], ['269', '270', '271'])).
% 1.52/1.74  thf('273', plain,
% 1.52/1.74      (((v2_struct_0 @ sk_A)
% 1.52/1.74        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74        | (v2_struct_0 @ sk_B)
% 1.52/1.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74            (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74            (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74               (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['266', '272'])).
% 1.52/1.74  thf('274', plain,
% 1.52/1.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.52/1.74         ((v2_struct_0 @ X25)
% 1.52/1.74          | ~ (v2_pre_topc @ X25)
% 1.52/1.74          | ~ (l1_pre_topc @ X25)
% 1.52/1.74          | (v2_struct_0 @ X26)
% 1.52/1.74          | ~ (m1_pre_topc @ X26 @ X27)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X26)
% 1.52/1.74          | ~ (v1_funct_1 @ X29)
% 1.52/1.74          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (m1_subset_1 @ X29 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 1.52/1.74             (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X30) @ X29)
% 1.52/1.74          | ((k3_funct_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X30 @ 
% 1.52/1.74              (sk_G @ X29 @ X30 @ X26 @ X28 @ X25))
% 1.52/1.74              != (k1_funct_1 @ X29 @ (sk_G @ X29 @ X30 @ X26 @ X28 @ X25)))
% 1.52/1.74          | ~ (m1_subset_1 @ X30 @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.52/1.74          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.52/1.74          | ~ (v1_funct_1 @ X30)
% 1.52/1.74          | ~ (m1_pre_topc @ X28 @ X27)
% 1.52/1.74          | (v2_struct_0 @ X28)
% 1.52/1.74          | ~ (l1_pre_topc @ X27)
% 1.52/1.74          | ~ (v2_pre_topc @ X27)
% 1.52/1.74          | (v2_struct_0 @ X27))),
% 1.52/1.74      inference('cnf', [status(esa)], [t73_tmap_1])).
% 1.52/1.74  thf('275', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74            (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74            != (k1_funct_1 @ sk_C @ 
% 1.52/1.74                (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.52/1.74          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74               (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | ~ (m1_subset_1 @ sk_C @ 
% 1.52/1.74               (k1_zfmisc_1 @ 
% 1.52/1.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.52/1.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.52/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['273', '274'])).
% 1.52/1.74  thf('276', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('clc', [status(thm)], ['119', '120'])).
% 1.52/1.74  thf('277', plain,
% 1.52/1.74      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.52/1.74        (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['111', '112'])).
% 1.52/1.74  thf('278', plain,
% 1.52/1.74      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('clc', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('279', plain,
% 1.52/1.74      ((m1_subset_1 @ sk_C @ 
% 1.52/1.74        (k1_zfmisc_1 @ 
% 1.52/1.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('280', plain,
% 1.52/1.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('282', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('283', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('284', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74            (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74            != (k1_funct_1 @ sk_C @ 
% 1.52/1.74                (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v2_struct_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)],
% 1.52/1.74                ['275', '276', '277', '278', '279', '280', '281', '282', '283'])).
% 1.52/1.74  thf('285', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.74             sk_C)
% 1.52/1.74          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (v2_pre_topc @ X0)
% 1.52/1.74          | (v2_struct_0 @ X0)
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.74          | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.52/1.74              (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.74              != (k1_funct_1 @ sk_C @ 
% 1.52/1.74                  (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 1.52/1.74      inference('simplify', [status(thm)], ['284'])).
% 1.52/1.74  thf('286', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.74            != (k1_funct_1 @ sk_C @ 
% 1.52/1.74                (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 1.52/1.74          | (v2_struct_0 @ sk_A)
% 1.52/1.74          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.74             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.74          | (v2_struct_0 @ sk_B)
% 1.52/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_A)
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.52/1.75      inference('sup-', [status(thm)], ['265', '285'])).
% 1.52/1.75  thf('287', plain,
% 1.52/1.75      (![X0 : $i]:
% 1.52/1.75         (~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_A)
% 1.52/1.75          | ((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.75              != (k1_funct_1 @ sk_C @ 
% 1.52/1.75                  (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 1.52/1.75      inference('simplify', [status(thm)], ['286'])).
% 1.52/1.75  thf('288', plain,
% 1.52/1.75      (![X0 : $i]:
% 1.52/1.75         (((sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 1.52/1.75            != (sk_G @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 1.52/1.75          | (v2_struct_0 @ sk_A)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (v2_struct_0 @ sk_A)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 1.52/1.75      inference('sup-', [status(thm)], ['254', '287'])).
% 1.52/1.75  thf('289', plain,
% 1.52/1.75      (![X0 : $i]:
% 1.52/1.75         (~ (m1_pre_topc @ sk_B @ sk_B)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_A))),
% 1.52/1.75      inference('simplify', [status(thm)], ['288'])).
% 1.52/1.75  thf('290', plain,
% 1.52/1.75      (![X0 : $i]:
% 1.52/1.75         (~ (l1_pre_topc @ sk_B)
% 1.52/1.75          | (v2_struct_0 @ sk_A)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C))),
% 1.52/1.75      inference('sup-', [status(thm)], ['2', '289'])).
% 1.52/1.75  thf('291', plain, ((l1_pre_topc @ sk_B)),
% 1.52/1.75      inference('demod', [status(thm)], ['127', '128'])).
% 1.52/1.75  thf('292', plain,
% 1.52/1.75      (![X0 : $i]:
% 1.52/1.75         ((v2_struct_0 @ sk_A)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75          | (v2_struct_0 @ sk_B)
% 1.52/1.75          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75          | (v2_struct_0 @ X0)
% 1.52/1.75          | ~ (v2_pre_topc @ X0)
% 1.52/1.75          | ~ (l1_pre_topc @ X0)
% 1.52/1.75          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.52/1.75          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75             sk_C))),
% 1.52/1.75      inference('demod', [status(thm)], ['290', '291'])).
% 1.52/1.75  thf('293', plain,
% 1.52/1.75      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75         (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 1.52/1.75         sk_C)
% 1.52/1.75        | ~ (l1_pre_topc @ sk_A)
% 1.52/1.75        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.75        | (v2_struct_0 @ sk_A)
% 1.52/1.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75        | (v2_struct_0 @ sk_B)
% 1.52/1.75        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75        | (v2_struct_0 @ sk_A))),
% 1.52/1.75      inference('sup-', [status(thm)], ['1', '292'])).
% 1.52/1.75  thf('294', plain,
% 1.52/1.75      (((k4_tmap_1 @ sk_A @ sk_B)
% 1.52/1.75         = (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.52/1.75      inference('demod', [status(thm)], ['158', '176', '194', '212'])).
% 1.52/1.75  thf('295', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('296', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('297', plain,
% 1.52/1.75      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75         (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75        | (v2_struct_0 @ sk_A)
% 1.52/1.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75        | (v2_struct_0 @ sk_B)
% 1.52/1.75        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.52/1.75        | (v2_struct_0 @ sk_A))),
% 1.52/1.75      inference('demod', [status(thm)], ['293', '294', '295', '296'])).
% 1.52/1.75  thf('298', plain,
% 1.52/1.75      (((v2_struct_0 @ sk_B)
% 1.52/1.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75        | (v2_struct_0 @ sk_A)
% 1.52/1.75        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C))),
% 1.52/1.75      inference('simplify', [status(thm)], ['297'])).
% 1.52/1.75  thf('299', plain,
% 1.52/1.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.52/1.75          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('300', plain,
% 1.52/1.75      (((v2_struct_0 @ sk_A)
% 1.52/1.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.52/1.75        | (v2_struct_0 @ sk_B))),
% 1.52/1.75      inference('sup-', [status(thm)], ['298', '299'])).
% 1.52/1.75  thf('301', plain, (~ (v2_struct_0 @ sk_A)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('302', plain,
% 1.52/1.75      (((v2_struct_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.52/1.75      inference('clc', [status(thm)], ['300', '301'])).
% 1.52/1.75  thf('303', plain, (~ (v2_struct_0 @ sk_B)),
% 1.52/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.75  thf('304', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.52/1.75      inference('clc', [status(thm)], ['302', '303'])).
% 1.52/1.75  thf(fc2_struct_0, axiom,
% 1.52/1.75    (![A:$i]:
% 1.52/1.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.52/1.75       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.52/1.75  thf('305', plain,
% 1.52/1.75      (![X13 : $i]:
% 1.52/1.75         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 1.52/1.75          | ~ (l1_struct_0 @ X13)
% 1.52/1.75          | (v2_struct_0 @ X13))),
% 1.52/1.75      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.52/1.75  thf('306', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.52/1.75      inference('sup-', [status(thm)], ['304', '305'])).
% 1.52/1.75  thf('307', plain, ((l1_pre_topc @ sk_B)),
% 1.52/1.75      inference('demod', [status(thm)], ['127', '128'])).
% 1.52/1.75  thf(dt_l1_pre_topc, axiom,
% 1.52/1.75    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.52/1.75  thf('308', plain,
% 1.52/1.75      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.52/1.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.52/1.75  thf('309', plain, ((l1_struct_0 @ sk_B)),
% 1.52/1.75      inference('sup-', [status(thm)], ['307', '308'])).
% 1.52/1.75  thf('310', plain, ((v2_struct_0 @ sk_B)),
% 1.52/1.75      inference('demod', [status(thm)], ['306', '309'])).
% 1.52/1.75  thf('311', plain, ($false), inference('demod', [status(thm)], ['0', '310'])).
% 1.52/1.75  
% 1.52/1.75  % SZS output end Refutation
% 1.52/1.75  
% 1.52/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
