%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hKTLJPAcBp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:41 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  309 (10988 expanded)
%              Number of leaves         :   39 (3201 expanded)
%              Depth                    :   43
%              Number of atoms          : 4520 (293297 expanded)
%              Number of equality atoms :   55 (5224 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t59_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('17',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14','22','30','35','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('45',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('46',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) @ X43 @ ( k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43 ) )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('49',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('56',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('57',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('58',plain,(
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

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('61',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('67',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('68',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('73',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('74',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('75',plain,(
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

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('78',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('79',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('80',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('97',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54','95','96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( X10 = X13 )
      | ~ ( r2_funct_2 @ X11 @ X12 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('108',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('112',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('113',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('114',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('117',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('123',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('124',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('128',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('134',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('136',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('137',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('138',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('141',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('147',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('148',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('152',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('158',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('160',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('161',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('162',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('165',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('171',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('172',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('176',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('177',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','134','158','181'])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','182','183','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('194',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('195',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('196',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('199',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('203',plain,(
    ! [X52: $i] :
      ( ~ ( r2_hidden @ X52 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( X52
        = ( k1_funct_1 @ sk_C @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['201','204'])).

thf('206',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','200'])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

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

thf('209',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X50 )
      | ~ ( r2_hidden @ X51 @ ( u1_struct_0 @ X49 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X50 @ X49 ) @ X51 )
        = X51 )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X50 ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('219',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('220',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['218','224'])).

thf('226',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('229',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ X7 )
      | ( ( k3_funct_2 @ X7 @ X8 @ X6 @ X9 )
        = ( k1_funct_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('232',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['227','233'])).

thf('235',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) )
       != ( k1_funct_1 @ X40 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('236',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','134','158','181'])).

thf('243',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('244',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('245',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('246',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('247',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('248',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241','242','243','244','245','246','247'])).

thf('249',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['217','249'])).

thf('251',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['206','251'])).

thf('253',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['192','253'])).

thf('255',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['191','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['0','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hKTLJPAcBp
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:42:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.23/2.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.23/2.42  % Solved by: fo/fo7.sh
% 2.23/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.23/2.42  % done 2856 iterations in 1.950s
% 2.23/2.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.23/2.42  % SZS output start Refutation
% 2.23/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.23/2.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.23/2.42  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.23/2.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.23/2.42  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.23/2.42  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 2.23/2.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.23/2.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.23/2.42  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.23/2.42  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 2.23/2.42  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.23/2.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.23/2.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.23/2.42  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 2.23/2.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.23/2.42  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 2.23/2.42  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.23/2.42  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.23/2.42  thf(sk_C_type, type, sk_C: $i).
% 2.23/2.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.23/2.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.23/2.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.23/2.42  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.23/2.42  thf(t96_tmap_1, conjecture,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( ( v1_funct_1 @ C ) & 
% 2.23/2.42                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.23/2.42                 ( m1_subset_1 @
% 2.23/2.42                   C @ 
% 2.23/2.42                   ( k1_zfmisc_1 @
% 2.23/2.42                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.23/2.42               ( ( ![D:$i]:
% 2.23/2.42                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.23/2.42                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.23/2.42                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.23/2.42                 ( r2_funct_2 @
% 2.23/2.42                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 2.23/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.23/2.42    (~( ![A:$i]:
% 2.23/2.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.23/2.42            ( l1_pre_topc @ A ) ) =>
% 2.23/2.42          ( ![B:$i]:
% 2.23/2.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.23/2.42              ( ![C:$i]:
% 2.23/2.42                ( ( ( v1_funct_1 @ C ) & 
% 2.23/2.42                    ( v1_funct_2 @
% 2.23/2.42                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.23/2.42                    ( m1_subset_1 @
% 2.23/2.42                      C @ 
% 2.23/2.42                      ( k1_zfmisc_1 @
% 2.23/2.42                        ( k2_zfmisc_1 @
% 2.23/2.42                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.23/2.42                  ( ( ![D:$i]:
% 2.23/2.42                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.23/2.42                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.23/2.42                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.23/2.42                    ( r2_funct_2 @
% 2.23/2.42                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 2.23/2.42    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 2.23/2.42  thf('0', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(t2_tsep_1, axiom,
% 2.23/2.42    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 2.23/2.42  thf('1', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('2', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('3', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(dt_k4_tmap_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.23/2.42         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.23/2.42       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 2.23/2.42         ( v1_funct_2 @
% 2.23/2.42           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.23/2.42         ( m1_subset_1 @
% 2.23/2.42           ( k4_tmap_1 @ A @ B ) @ 
% 2.23/2.42           ( k1_zfmisc_1 @
% 2.23/2.42             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.23/2.42  thf('4', plain,
% 2.23/2.42      (![X32 : $i, X33 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ X32)
% 2.23/2.42          | ~ (v2_pre_topc @ X32)
% 2.23/2.42          | (v2_struct_0 @ X32)
% 2.23/2.42          | ~ (m1_pre_topc @ X33 @ X32)
% 2.23/2.42          | (m1_subset_1 @ (k4_tmap_1 @ X32 @ X33) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.23/2.42  thf('5', plain,
% 2.23/2.42      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['3', '4'])).
% 2.23/2.42  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('8', plain,
% 2.23/2.42      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.23/2.42  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('10', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(t59_tmap_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.23/2.42             ( l1_pre_topc @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 2.23/2.42               ( ![D:$i]:
% 2.23/2.42                 ( ( ( v1_funct_1 @ D ) & 
% 2.23/2.42                     ( v1_funct_2 @
% 2.23/2.42                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.23/2.42                     ( m1_subset_1 @
% 2.23/2.42                       D @ 
% 2.23/2.42                       ( k1_zfmisc_1 @
% 2.23/2.42                         ( k2_zfmisc_1 @
% 2.23/2.42                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.23/2.42                   ( ![E:$i]:
% 2.23/2.42                     ( ( ( v1_funct_1 @ E ) & 
% 2.23/2.42                         ( v1_funct_2 @
% 2.23/2.42                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 2.23/2.42                         ( m1_subset_1 @
% 2.23/2.42                           E @ 
% 2.23/2.42                           ( k1_zfmisc_1 @
% 2.23/2.42                             ( k2_zfmisc_1 @
% 2.23/2.42                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.23/2.42                       ( ( ![F:$i]:
% 2.23/2.42                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 2.23/2.42                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 2.23/2.42                               ( ( k3_funct_2 @
% 2.23/2.42                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                                   D @ F ) =
% 2.23/2.42                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 2.23/2.42                         ( r2_funct_2 @
% 2.23/2.42                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 2.23/2.42                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('11', plain,
% 2.23/2.42      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X37)
% 2.23/2.42          | ~ (v2_pre_topc @ X37)
% 2.23/2.42          | ~ (l1_pre_topc @ X37)
% 2.23/2.42          | ~ (v1_funct_1 @ X38)
% 2.23/2.42          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 2.23/2.42          | ~ (m1_subset_1 @ X38 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 2.23/2.42          | (r2_hidden @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39) @ 
% 2.23/2.42             (u1_struct_0 @ X41))
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 2.23/2.42             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 2.23/2.42          | ~ (m1_subset_1 @ X40 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 2.23/2.42          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 2.23/2.42          | ~ (v1_funct_1 @ X40)
% 2.23/2.42          | ~ (m1_pre_topc @ X41 @ X37)
% 2.23/2.42          | (v2_struct_0 @ X41)
% 2.23/2.42          | ~ (l1_pre_topc @ X39)
% 2.23/2.42          | ~ (v2_pre_topc @ X39)
% 2.23/2.42          | (v2_struct_0 @ X39))),
% 2.23/2.42      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.23/2.42  thf('12', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ X0)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ~ (v1_funct_1 @ X1)
% 2.23/2.42          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (m1_subset_1 @ X1 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.23/2.42             X1)
% 2.23/2.42          | (r2_hidden @ 
% 2.23/2.42             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42             (u1_struct_0 @ X0))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['10', '11'])).
% 2.23/2.42  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('15', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('16', plain,
% 2.23/2.42      (![X32 : $i, X33 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ X32)
% 2.23/2.42          | ~ (v2_pre_topc @ X32)
% 2.23/2.42          | (v2_struct_0 @ X32)
% 2.23/2.42          | ~ (m1_pre_topc @ X33 @ X32)
% 2.23/2.42          | (v1_funct_2 @ (k4_tmap_1 @ X32 @ X33) @ (u1_struct_0 @ X33) @ 
% 2.23/2.42             (u1_struct_0 @ X32)))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.23/2.42  thf('17', plain,
% 2.23/2.42      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42         (u1_struct_0 @ sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['15', '16'])).
% 2.23/2.42  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('20', plain,
% 2.23/2.42      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42         (u1_struct_0 @ sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.23/2.42  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('22', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('23', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('24', plain,
% 2.23/2.42      (![X32 : $i, X33 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ X32)
% 2.23/2.42          | ~ (v2_pre_topc @ X32)
% 2.23/2.42          | (v2_struct_0 @ X32)
% 2.23/2.42          | ~ (m1_pre_topc @ X33 @ X32)
% 2.23/2.42          | (v1_funct_1 @ (k4_tmap_1 @ X32 @ X33)))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.23/2.42  thf('25', plain,
% 2.23/2.42      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['23', '24'])).
% 2.23/2.42  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('28', plain,
% 2.23/2.42      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.23/2.42  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('30', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(dt_m1_pre_topc, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( l1_pre_topc @ A ) =>
% 2.23/2.42       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.23/2.42  thf('32', plain,
% 2.23/2.42      (![X16 : $i, X17 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X16 @ X17)
% 2.23/2.42          | (l1_pre_topc @ X16)
% 2.23/2.42          | ~ (l1_pre_topc @ X17))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.23/2.42  thf('33', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['31', '32'])).
% 2.23/2.42  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('35', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('36', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(cc1_pre_topc, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 2.23/2.42  thf('37', plain,
% 2.23/2.42      (![X14 : $i, X15 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X14 @ X15)
% 2.23/2.42          | (v2_pre_topc @ X14)
% 2.23/2.42          | ~ (l1_pre_topc @ X15)
% 2.23/2.42          | ~ (v2_pre_topc @ X15))),
% 2.23/2.42      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 2.23/2.42  thf('38', plain,
% 2.23/2.42      ((~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42        | (v2_pre_topc @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['36', '37'])).
% 2.23/2.42  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('41', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('42', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ X0)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ~ (v1_funct_1 @ X1)
% 2.23/2.42          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (m1_subset_1 @ X1 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.23/2.42             X1)
% 2.23/2.42          | (r2_hidden @ 
% 2.23/2.42             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42             (u1_struct_0 @ X0))
% 2.23/2.42          | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)],
% 2.23/2.42                ['12', '13', '14', '22', '30', '35', '41'])).
% 2.23/2.42  thf('43', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42           sk_C)
% 2.23/2.42        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['2', '42'])).
% 2.23/2.42  thf('44', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('45', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(t74_tmap_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.23/2.42             ( l1_pre_topc @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.23/2.42               ( ![D:$i]:
% 2.23/2.42                 ( ( ( v1_funct_1 @ D ) & 
% 2.23/2.42                     ( v1_funct_2 @
% 2.23/2.42                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42                     ( m1_subset_1 @
% 2.23/2.42                       D @ 
% 2.23/2.42                       ( k1_zfmisc_1 @
% 2.23/2.42                         ( k2_zfmisc_1 @
% 2.23/2.42                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42                   ( r2_funct_2 @
% 2.23/2.42                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 2.23/2.42                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('46', plain,
% 2.23/2.42      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X42)
% 2.23/2.42          | ~ (v2_pre_topc @ X42)
% 2.23/2.42          | ~ (l1_pre_topc @ X42)
% 2.23/2.42          | ~ (v1_funct_1 @ X43)
% 2.23/2.42          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 2.23/2.42          | ~ (m1_subset_1 @ X43 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42) @ X43 @ 
% 2.23/2.42             (k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43))
% 2.23/2.42          | ~ (m1_pre_topc @ X44 @ X45)
% 2.23/2.42          | (v2_struct_0 @ X44)
% 2.23/2.42          | ~ (l1_pre_topc @ X45)
% 2.23/2.42          | ~ (v2_pre_topc @ X45)
% 2.23/2.42          | (v2_struct_0 @ X45))),
% 2.23/2.42      inference('cnf', [status(esa)], [t74_tmap_1])).
% 2.23/2.42  thf('47', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42             (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['45', '46'])).
% 2.23/2.42  thf('48', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('49', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('52', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42             (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 2.23/2.42  thf('53', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['44', '52'])).
% 2.23/2.42  thf('54', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('55', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('56', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('57', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(d5_tmap_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.23/2.42             ( l1_pre_topc @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( m1_pre_topc @ C @ A ) =>
% 2.23/2.42               ( ![D:$i]:
% 2.23/2.42                 ( ( m1_pre_topc @ D @ A ) =>
% 2.23/2.42                   ( ![E:$i]:
% 2.23/2.42                     ( ( ( v1_funct_1 @ E ) & 
% 2.23/2.42                         ( v1_funct_2 @
% 2.23/2.42                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42                         ( m1_subset_1 @
% 2.23/2.42                           E @ 
% 2.23/2.42                           ( k1_zfmisc_1 @
% 2.23/2.42                             ( k2_zfmisc_1 @
% 2.23/2.42                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42                       ( ( m1_pre_topc @ D @ C ) =>
% 2.23/2.42                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 2.23/2.42                           ( k2_partfun1 @
% 2.23/2.42                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 2.23/2.42                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('58', plain,
% 2.23/2.42      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X22)
% 2.23/2.42          | ~ (v2_pre_topc @ X22)
% 2.23/2.42          | ~ (l1_pre_topc @ X22)
% 2.23/2.42          | ~ (m1_pre_topc @ X23 @ X24)
% 2.23/2.42          | ~ (m1_pre_topc @ X23 @ X25)
% 2.23/2.42          | ((k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26)
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 2.23/2.42                 X26 @ (u1_struct_0 @ X23)))
% 2.23/2.42          | ~ (m1_subset_1 @ X26 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))))
% 2.23/2.42          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))
% 2.23/2.42          | ~ (v1_funct_1 @ X26)
% 2.23/2.42          | ~ (m1_pre_topc @ X25 @ X24)
% 2.23/2.42          | ~ (l1_pre_topc @ X24)
% 2.23/2.42          | ~ (v2_pre_topc @ X24)
% 2.23/2.42          | (v2_struct_0 @ X24))),
% 2.23/2.42      inference('cnf', [status(esa)], [d5_tmap_1])).
% 2.23/2.42  thf('59', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X1)))
% 2.23/2.42          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X1 @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['57', '58'])).
% 2.23/2.42  thf('60', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('61', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('64', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X1)))
% 2.23/2.42          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X1 @ X0)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 2.23/2.42  thf('65', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['56', '64'])).
% 2.23/2.42  thf('66', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('67', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('68', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('69', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.23/2.42          | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 2.23/2.42  thf('70', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_B_1)
% 2.23/2.42          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('simplify', [status(thm)], ['69'])).
% 2.23/2.42  thf('71', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['55', '70'])).
% 2.23/2.42  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('73', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('74', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(d4_tmap_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.23/2.42             ( l1_pre_topc @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( ( v1_funct_1 @ C ) & 
% 2.23/2.42                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42                 ( m1_subset_1 @
% 2.23/2.42                   C @ 
% 2.23/2.42                   ( k1_zfmisc_1 @
% 2.23/2.42                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42               ( ![D:$i]:
% 2.23/2.42                 ( ( m1_pre_topc @ D @ A ) =>
% 2.23/2.42                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 2.23/2.42                     ( k2_partfun1 @
% 2.23/2.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.23/2.42                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('75', plain,
% 2.23/2.42      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X18)
% 2.23/2.42          | ~ (v2_pre_topc @ X18)
% 2.23/2.42          | ~ (l1_pre_topc @ X18)
% 2.23/2.42          | ~ (m1_pre_topc @ X19 @ X20)
% 2.23/2.42          | ((k2_tmap_1 @ X20 @ X18 @ X21 @ X19)
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18) @ 
% 2.23/2.42                 X21 @ (u1_struct_0 @ X19)))
% 2.23/2.42          | ~ (m1_subset_1 @ X21 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))))
% 2.23/2.42          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X18))
% 2.23/2.42          | ~ (v1_funct_1 @ X21)
% 2.23/2.42          | ~ (l1_pre_topc @ X20)
% 2.23/2.42          | ~ (v2_pre_topc @ X20)
% 2.23/2.42          | (v2_struct_0 @ X20))),
% 2.23/2.42      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.23/2.42  thf('76', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['74', '75'])).
% 2.23/2.42  thf('77', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('78', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('79', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('80', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('83', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_B_1)
% 2.23/2.42          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)],
% 2.23/2.42                ['76', '77', '78', '79', '80', '81', '82'])).
% 2.23/2.42  thf('84', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.23/2.42            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['73', '83'])).
% 2.23/2.42  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('86', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.23/2.42            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['84', '85'])).
% 2.23/2.42  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('88', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.23/2.42            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.23/2.42      inference('clc', [status(thm)], ['86', '87'])).
% 2.23/2.42  thf('89', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('90', plain,
% 2.23/2.42      (((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.23/2.42         = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('clc', [status(thm)], ['88', '89'])).
% 2.23/2.42  thf('91', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['71', '72', '90'])).
% 2.23/2.42  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('93', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.23/2.42      inference('clc', [status(thm)], ['91', '92'])).
% 2.23/2.42  thf('94', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('95', plain,
% 2.23/2.42      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['93', '94'])).
% 2.23/2.42  thf('96', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('97', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('98', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['53', '54', '95', '96', '97'])).
% 2.23/2.42  thf('99', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('simplify', [status(thm)], ['98'])).
% 2.23/2.42  thf('100', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('101', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.23/2.42      inference('clc', [status(thm)], ['99', '100'])).
% 2.23/2.42  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('103', plain,
% 2.23/2.42      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42        (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['101', '102'])).
% 2.23/2.42  thf('104', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(redefinition_r2_funct_2, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i,D:$i]:
% 2.23/2.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.42         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.23/2.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.42       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.23/2.42  thf('105', plain,
% 2.23/2.42      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.42          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 2.23/2.42          | ~ (v1_funct_1 @ X10)
% 2.23/2.42          | ~ (v1_funct_1 @ X13)
% 2.23/2.42          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 2.23/2.42          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.23/2.42          | ((X10) = (X13))
% 2.23/2.42          | ~ (r2_funct_2 @ X11 @ X12 @ X10 @ X13))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.23/2.42  thf('106', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42          | ((k4_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.23/2.42          | ~ (m1_subset_1 @ X0 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ X0)
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['104', '105'])).
% 2.23/2.42  thf('107', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('108', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('109', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42          | ((k4_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.23/2.42          | ~ (m1_subset_1 @ X0 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ X0))),
% 2.23/2.42      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.23/2.42  thf('110', plain,
% 2.23/2.42      ((~ (v1_funct_1 @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.23/2.42        | ~ (v1_funct_2 @ 
% 2.23/2.42             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (m1_subset_1 @ 
% 2.23/2.42             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | ((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.23/2.42            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['103', '109'])).
% 2.23/2.42  thf('111', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('112', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('113', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(dt_k3_tmap_1, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.23/2.42         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.23/2.42         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 2.23/2.42         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 2.23/2.42         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.23/2.42         ( m1_subset_1 @
% 2.23/2.42           E @ 
% 2.23/2.42           ( k1_zfmisc_1 @
% 2.23/2.42             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.23/2.42       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 2.23/2.42         ( v1_funct_2 @
% 2.23/2.42           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 2.23/2.42           ( u1_struct_0 @ B ) ) & 
% 2.23/2.42         ( m1_subset_1 @
% 2.23/2.42           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 2.23/2.42           ( k1_zfmisc_1 @
% 2.23/2.42             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.23/2.42  thf('114', plain,
% 2.23/2.42      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X27 @ X28)
% 2.23/2.42          | ~ (m1_pre_topc @ X29 @ X28)
% 2.23/2.42          | ~ (l1_pre_topc @ X30)
% 2.23/2.42          | ~ (v2_pre_topc @ X30)
% 2.23/2.42          | (v2_struct_0 @ X30)
% 2.23/2.42          | ~ (l1_pre_topc @ X28)
% 2.23/2.42          | ~ (v2_pre_topc @ X28)
% 2.23/2.42          | (v2_struct_0 @ X28)
% 2.23/2.42          | ~ (v1_funct_1 @ X31)
% 2.23/2.42          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 2.23/2.42          | ~ (m1_subset_1 @ X31 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 2.23/2.42          | (v1_funct_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31)))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.23/2.42  thf('115', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v1_funct_1 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['113', '114'])).
% 2.23/2.42  thf('116', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('117', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('120', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v1_funct_1 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 2.23/2.42  thf('121', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (v1_funct_1 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['112', '120'])).
% 2.23/2.42  thf('122', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('123', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('124', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('125', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (v1_funct_1 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.23/2.42      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 2.23/2.42  thf('126', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v1_funct_1 @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['111', '125'])).
% 2.23/2.42  thf('127', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('128', plain,
% 2.23/2.42      (((v1_funct_1 @ 
% 2.23/2.42         (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42          (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['126', '127'])).
% 2.23/2.42  thf('129', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('130', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_funct_1 @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.23/2.42      inference('clc', [status(thm)], ['128', '129'])).
% 2.23/2.42  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('132', plain,
% 2.23/2.42      ((v1_funct_1 @ 
% 2.23/2.42        (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 2.23/2.42      inference('clc', [status(thm)], ['130', '131'])).
% 2.23/2.42  thf('133', plain,
% 2.23/2.42      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['93', '94'])).
% 2.23/2.42  thf('134', plain,
% 2.23/2.42      ((v1_funct_1 @ 
% 2.23/2.42        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['132', '133'])).
% 2.23/2.42  thf('135', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('136', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('137', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf('138', plain,
% 2.23/2.42      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X27 @ X28)
% 2.23/2.42          | ~ (m1_pre_topc @ X29 @ X28)
% 2.23/2.42          | ~ (l1_pre_topc @ X30)
% 2.23/2.42          | ~ (v2_pre_topc @ X30)
% 2.23/2.42          | (v2_struct_0 @ X30)
% 2.23/2.42          | ~ (l1_pre_topc @ X28)
% 2.23/2.42          | ~ (v2_pre_topc @ X28)
% 2.23/2.42          | (v2_struct_0 @ X28)
% 2.23/2.42          | ~ (v1_funct_1 @ X31)
% 2.23/2.42          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 2.23/2.42          | ~ (m1_subset_1 @ X31 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 2.23/2.42          | (v1_funct_2 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 2.23/2.42             (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.23/2.42  thf('139', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v1_funct_2 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['137', '138'])).
% 2.23/2.42  thf('140', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('141', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('144', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((v1_funct_2 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 2.23/2.42  thf('145', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (v1_funct_2 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['136', '144'])).
% 2.23/2.42  thf('146', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('147', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('148', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('149', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (v1_funct_2 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 2.23/2.42  thf('150', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v1_funct_2 @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['135', '149'])).
% 2.23/2.42  thf('151', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('152', plain,
% 2.23/2.42      (((v1_funct_2 @ 
% 2.23/2.42         (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42          (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42         (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['150', '151'])).
% 2.23/2.42  thf('153', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('154', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_funct_2 @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('clc', [status(thm)], ['152', '153'])).
% 2.23/2.42  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('156', plain,
% 2.23/2.42      ((v1_funct_2 @ 
% 2.23/2.42        (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42        (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['154', '155'])).
% 2.23/2.42  thf('157', plain,
% 2.23/2.42      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['93', '94'])).
% 2.23/2.42  thf('158', plain,
% 2.23/2.42      ((v1_funct_2 @ 
% 2.23/2.42        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['156', '157'])).
% 2.23/2.42  thf('159', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('160', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('161', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf('162', plain,
% 2.23/2.42      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X27 @ X28)
% 2.23/2.42          | ~ (m1_pre_topc @ X29 @ X28)
% 2.23/2.42          | ~ (l1_pre_topc @ X30)
% 2.23/2.42          | ~ (v2_pre_topc @ X30)
% 2.23/2.42          | (v2_struct_0 @ X30)
% 2.23/2.42          | ~ (l1_pre_topc @ X28)
% 2.23/2.42          | ~ (v2_pre_topc @ X28)
% 2.23/2.42          | (v2_struct_0 @ X28)
% 2.23/2.42          | ~ (v1_funct_1 @ X31)
% 2.23/2.42          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 2.23/2.42          | ~ (m1_subset_1 @ X31 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 2.23/2.42          | (m1_subset_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.23/2.42  thf('163', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((m1_subset_1 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['161', '162'])).
% 2.23/2.42  thf('164', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('165', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('168', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         ((m1_subset_1 @ 
% 2.23/2.42           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42          | (v2_struct_0 @ X1)
% 2.23/2.42          | ~ (v2_pre_topc @ X1)
% 2.23/2.42          | ~ (l1_pre_topc @ X1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.23/2.42      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 2.23/2.42  thf('169', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42          | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (m1_subset_1 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['160', '168'])).
% 2.23/2.42  thf('170', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('171', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('172', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('173', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ sk_A)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (m1_subset_1 @ 
% 2.23/2.42             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.23/2.42              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.23/2.42      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 2.23/2.42  thf('174', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['159', '173'])).
% 2.23/2.42  thf('175', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('176', plain,
% 2.23/2.42      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['93', '94'])).
% 2.23/2.42  thf('177', plain,
% 2.23/2.42      (((m1_subset_1 @ 
% 2.23/2.42         (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42         (k1_zfmisc_1 @ 
% 2.23/2.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['174', '175', '176'])).
% 2.23/2.42  thf('178', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('179', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42           (k1_zfmisc_1 @ 
% 2.23/2.42            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))))),
% 2.23/2.42      inference('clc', [status(thm)], ['177', '178'])).
% 2.23/2.42  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('181', plain,
% 2.23/2.42      ((m1_subset_1 @ 
% 2.23/2.42        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['179', '180'])).
% 2.23/2.42  thf('182', plain,
% 2.23/2.42      (((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['110', '134', '158', '181'])).
% 2.23/2.42  thf('183', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('185', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['43', '182', '183', '184'])).
% 2.23/2.42  thf('186', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('simplify', [status(thm)], ['185'])).
% 2.23/2.42  thf('187', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['1', '186'])).
% 2.23/2.42  thf('188', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('189', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf(d1_xboole_0, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.23/2.42  thf('190', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.23/2.42      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.23/2.42  thf('191', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['189', '190'])).
% 2.23/2.42  thf('192', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('193', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf('194', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf(t1_tsep_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( l1_pre_topc @ A ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( m1_pre_topc @ B @ A ) =>
% 2.23/2.42           ( m1_subset_1 @
% 2.23/2.42             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.23/2.42  thf('195', plain,
% 2.23/2.42      (![X34 : $i, X35 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X34 @ X35)
% 2.23/2.42          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 2.23/2.42             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.23/2.42          | ~ (l1_pre_topc @ X35))),
% 2.23/2.42      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.23/2.42  thf('196', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_A)
% 2.23/2.42        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['194', '195'])).
% 2.23/2.42  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('198', plain,
% 2.23/2.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('demod', [status(thm)], ['196', '197'])).
% 2.23/2.42  thf(t4_subset, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i]:
% 2.23/2.42     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.23/2.42       ( m1_subset_1 @ A @ C ) ))).
% 2.23/2.42  thf('199', plain,
% 2.23/2.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.23/2.42         (~ (r2_hidden @ X3 @ X4)
% 2.23/2.42          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.23/2.42          | (m1_subset_1 @ X3 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t4_subset])).
% 2.23/2.42  thf('200', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.23/2.42          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['198', '199'])).
% 2.23/2.42  thf('201', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['193', '200'])).
% 2.23/2.42  thf('202', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf('203', plain,
% 2.23/2.42      (![X52 : $i]:
% 2.23/2.42         (~ (r2_hidden @ X52 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42          | ((X52) = (k1_funct_1 @ sk_C @ X52))
% 2.23/2.42          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('204', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (m1_subset_1 @ 
% 2.23/2.42             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42              sk_A) @ 
% 2.23/2.42             (u1_struct_0 @ sk_A))
% 2.23/2.42        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42            = (k1_funct_1 @ sk_C @ 
% 2.23/2.42               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                sk_A))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['202', '203'])).
% 2.23/2.42  thf('205', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42            = (k1_funct_1 @ sk_C @ 
% 2.23/2.42               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                sk_A)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['201', '204'])).
% 2.23/2.42  thf('206', plain,
% 2.23/2.42      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42          = (k1_funct_1 @ sk_C @ 
% 2.23/2.42             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42              sk_A)))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('simplify', [status(thm)], ['205'])).
% 2.23/2.42  thf('207', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['193', '200'])).
% 2.23/2.42  thf('208', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf(t95_tmap_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.23/2.42               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 2.23/2.42                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('209', plain,
% 2.23/2.42      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X49)
% 2.23/2.42          | ~ (m1_pre_topc @ X49 @ X50)
% 2.23/2.42          | ~ (r2_hidden @ X51 @ (u1_struct_0 @ X49))
% 2.23/2.42          | ((k1_funct_1 @ (k4_tmap_1 @ X50 @ X49) @ X51) = (X51))
% 2.23/2.42          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X50))
% 2.23/2.42          | ~ (l1_pre_topc @ X50)
% 2.23/2.42          | ~ (v2_pre_topc @ X50)
% 2.23/2.42          | (v2_struct_0 @ X50))),
% 2.23/2.42      inference('cnf', [status(esa)], [t95_tmap_1])).
% 2.23/2.42  thf('210', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((v2_struct_0 @ sk_A)
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (v2_struct_0 @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | ~ (m1_subset_1 @ 
% 2.23/2.42               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                sk_A) @ 
% 2.23/2.42               (u1_struct_0 @ X0))
% 2.23/2.42          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 2.23/2.42              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A))
% 2.23/2.42              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                 sk_A))
% 2.23/2.42          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['208', '209'])).
% 2.23/2.42  thf('211', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.23/2.42          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 2.23/2.42              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A))
% 2.23/2.42              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                 sk_A))
% 2.23/2.42          | ~ (m1_subset_1 @ 
% 2.23/2.42               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                sk_A) @ 
% 2.23/2.42               (u1_struct_0 @ X0))
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | ~ (v2_pre_topc @ X0)
% 2.23/2.42          | (v2_struct_0 @ X0)
% 2.23/2.42          | (v2_struct_0 @ sk_B_1)
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42          | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('simplify', [status(thm)], ['210'])).
% 2.23/2.42  thf('212', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A))
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 2.23/2.42      inference('sup-', [status(thm)], ['207', '211'])).
% 2.23/2.42  thf('213', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('215', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('216', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A)))),
% 2.23/2.42      inference('demod', [status(thm)], ['212', '213', '214', '215'])).
% 2.23/2.42  thf('217', plain,
% 2.23/2.42      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42          = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('simplify', [status(thm)], ['216'])).
% 2.23/2.42  thf('218', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_hidden @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A))),
% 2.23/2.42      inference('demod', [status(thm)], ['187', '188'])).
% 2.23/2.42  thf('219', plain,
% 2.23/2.42      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.23/2.42      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.23/2.42  thf('220', plain,
% 2.23/2.42      (![X34 : $i, X35 : $i]:
% 2.23/2.42         (~ (m1_pre_topc @ X34 @ X35)
% 2.23/2.42          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 2.23/2.42             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.23/2.42          | ~ (l1_pre_topc @ X35))),
% 2.23/2.42      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.23/2.42  thf('221', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ X0)
% 2.23/2.42          | ~ (l1_pre_topc @ X0)
% 2.23/2.42          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.23/2.42             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['219', '220'])).
% 2.23/2.42  thf('222', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.23/2.42           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.23/2.42          | ~ (l1_pre_topc @ X0))),
% 2.23/2.42      inference('simplify', [status(thm)], ['221'])).
% 2.23/2.42  thf('223', plain,
% 2.23/2.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.23/2.42         (~ (r2_hidden @ X3 @ X4)
% 2.23/2.42          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.23/2.42          | (m1_subset_1 @ X3 @ X5))),
% 2.23/2.42      inference('cnf', [status(esa)], [t4_subset])).
% 2.23/2.42  thf('224', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (~ (l1_pre_topc @ X0)
% 2.23/2.42          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.23/2.42          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['222', '223'])).
% 2.23/2.42  thf('225', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | ~ (l1_pre_topc @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['218', '224'])).
% 2.23/2.42  thf('226', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('227', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (m1_subset_1 @ 
% 2.23/2.42           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.23/2.42           (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('demod', [status(thm)], ['225', '226'])).
% 2.23/2.42  thf('228', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf(redefinition_k3_funct_2, axiom,
% 2.23/2.42    (![A:$i,B:$i,C:$i,D:$i]:
% 2.23/2.42     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 2.23/2.42         ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.42         ( m1_subset_1 @ D @ A ) ) =>
% 2.23/2.42       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 2.23/2.42  thf('229', plain,
% 2.23/2.42      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.23/2.42         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 2.23/2.42          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 2.23/2.42          | ~ (v1_funct_1 @ X6)
% 2.23/2.42          | (v1_xboole_0 @ X7)
% 2.23/2.42          | ~ (m1_subset_1 @ X9 @ X7)
% 2.23/2.42          | ((k3_funct_2 @ X7 @ X8 @ X6 @ X9) = (k1_funct_1 @ X6 @ X9)))),
% 2.23/2.42      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 2.23/2.42  thf('230', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0))
% 2.23/2.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['228', '229'])).
% 2.23/2.42  thf('231', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('232', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('233', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.23/2.42            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0))
% 2.23/2.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('demod', [status(thm)], ['230', '231', '232'])).
% 2.23/2.42  thf('234', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | ((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42            (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                sk_A))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['227', '233'])).
% 2.23/2.42  thf('235', plain,
% 2.23/2.42      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.23/2.42         ((v2_struct_0 @ X37)
% 2.23/2.42          | ~ (v2_pre_topc @ X37)
% 2.23/2.42          | ~ (l1_pre_topc @ X37)
% 2.23/2.42          | ~ (v1_funct_1 @ X38)
% 2.23/2.42          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 2.23/2.42          | ~ (m1_subset_1 @ X38 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 2.23/2.42          | ((k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X38 @ 
% 2.23/2.42              (sk_F @ X40 @ X38 @ X41 @ X37 @ X39))
% 2.23/2.42              != (k1_funct_1 @ X40 @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39)))
% 2.23/2.42          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 2.23/2.42             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 2.23/2.42          | ~ (m1_subset_1 @ X40 @ 
% 2.23/2.42               (k1_zfmisc_1 @ 
% 2.23/2.42                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 2.23/2.42          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 2.23/2.42          | ~ (v1_funct_1 @ X40)
% 2.23/2.42          | ~ (m1_pre_topc @ X41 @ X37)
% 2.23/2.42          | (v2_struct_0 @ X41)
% 2.23/2.42          | ~ (l1_pre_topc @ X39)
% 2.23/2.42          | ~ (v2_pre_topc @ X39)
% 2.23/2.42          | (v2_struct_0 @ X39))),
% 2.23/2.42      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.23/2.42  thf('236', plain,
% 2.23/2.42      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42          != (k1_funct_1 @ sk_C @ 
% 2.23/2.42              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A)))
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_A)
% 2.23/2.42        | ~ (l1_pre_topc @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.23/2.42        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (m1_subset_1 @ sk_C @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.23/2.42           sk_C)
% 2.23/2.42        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42             (k1_zfmisc_1 @ 
% 2.23/2.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.23/2.42        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.23/2.42        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.23/2.42        | ~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | ~ (v2_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['234', '235'])).
% 2.23/2.42  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('240', plain,
% 2.23/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('241', plain,
% 2.23/2.42      ((m1_subset_1 @ sk_C @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('242', plain,
% 2.23/2.42      (((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.23/2.42         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['110', '134', '158', '181'])).
% 2.23/2.42  thf('243', plain,
% 2.23/2.42      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42        (k1_zfmisc_1 @ 
% 2.23/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.23/2.42      inference('clc', [status(thm)], ['8', '9'])).
% 2.23/2.42  thf('244', plain,
% 2.23/2.42      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.23/2.42        (u1_struct_0 @ sk_A))),
% 2.23/2.42      inference('clc', [status(thm)], ['20', '21'])).
% 2.23/2.42  thf('245', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['28', '29'])).
% 2.23/2.42  thf('246', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('247', plain, ((v2_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.23/2.42  thf('248', plain,
% 2.23/2.42      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42          != (k1_funct_1 @ sk_C @ 
% 2.23/2.42              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A)))
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)],
% 2.23/2.42                ['236', '237', '238', '239', '240', '241', '242', '243', 
% 2.23/2.42                 '244', '245', '246', '247'])).
% 2.23/2.42  thf('249', plain,
% 2.23/2.42      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.23/2.42            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.23/2.42            != (k1_funct_1 @ sk_C @ 
% 2.23/2.42                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                 sk_A))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['248'])).
% 2.23/2.42  thf('250', plain,
% 2.23/2.42      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42          != (k1_funct_1 @ sk_C @ 
% 2.23/2.42              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42               sk_A)))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['217', '249'])).
% 2.23/2.42  thf('251', plain,
% 2.23/2.42      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42            != (k1_funct_1 @ sk_C @ 
% 2.23/2.42                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42                 sk_A))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['250'])).
% 2.23/2.42  thf('252', plain,
% 2.23/2.42      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.23/2.42          != (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.23/2.42              sk_A))
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['206', '251'])).
% 2.23/2.42  thf('253', plain,
% 2.23/2.42      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('simplify', [status(thm)], ['252'])).
% 2.23/2.42  thf('254', plain,
% 2.23/2.42      ((~ (l1_pre_topc @ sk_B_1)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['192', '253'])).
% 2.23/2.42  thf('255', plain, ((l1_pre_topc @ sk_B_1)),
% 2.23/2.42      inference('demod', [status(thm)], ['33', '34'])).
% 2.23/2.42  thf('256', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('demod', [status(thm)], ['254', '255'])).
% 2.23/2.42  thf('257', plain,
% 2.23/2.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('258', plain,
% 2.23/2.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.23/2.42        | (v2_struct_0 @ sk_A)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('sup-', [status(thm)], ['256', '257'])).
% 2.23/2.42  thf('259', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('260', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.23/2.42      inference('clc', [status(thm)], ['258', '259'])).
% 2.23/2.42  thf('261', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('262', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('clc', [status(thm)], ['260', '261'])).
% 2.23/2.42  thf('263', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_A)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.23/2.42        | (v2_struct_0 @ sk_B_1))),
% 2.23/2.42      inference('demod', [status(thm)], ['191', '262'])).
% 2.23/2.42  thf('264', plain, (~ (v2_struct_0 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('265', plain,
% 2.23/2.42      (((v2_struct_0 @ sk_B_1)
% 2.23/2.42        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C))),
% 2.23/2.42      inference('clc', [status(thm)], ['263', '264'])).
% 2.23/2.42  thf('266', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('267', plain,
% 2.23/2.42      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.23/2.42        (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.23/2.42      inference('clc', [status(thm)], ['265', '266'])).
% 2.23/2.42  thf('268', plain, ($false), inference('demod', [status(thm)], ['0', '267'])).
% 2.23/2.42  
% 2.23/2.42  % SZS output end Refutation
% 2.23/2.42  
% 2.23/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
