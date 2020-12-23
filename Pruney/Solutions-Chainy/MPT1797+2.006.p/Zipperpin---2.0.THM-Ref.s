%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DQoIAp1xK8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:53 EST 2020

% Result     : Theorem 3.96s
% Output     : Refutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  349 (32350 expanded)
%              Number of leaves         :   49 (9151 expanded)
%              Depth                    :   29
%              Number of atoms          : 4294 (870691 expanded)
%              Number of equality atoms :  132 (8421 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t113_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
              & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
                & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
                & ( v5_pre_topc @ ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) )
                & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_tmap_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X33 @ X34 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k7_tmap_1 @ X30 @ X29 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ sk_B )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ sk_B )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X36 @ X35 ) )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','10','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t106_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_pre_topc @ X40 @ X41 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) )
        = ( k6_tmap_1 @ X41 @ X40 ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t62_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v5_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) @ X8 )
      | ( v5_pre_topc @ X11 @ X10 @ X8 )
      | ( X11 != X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ( v5_pre_topc @ X9 @ X10 @ X8 )
      | ~ ( v5_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('41',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('49',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('56',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['38','46','54','55','56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v5_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','58'])).

thf('60',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('64',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('65',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( v5_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ( v5_pre_topc @ X0 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X33 @ X34 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('71',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('73',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('81',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('88',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','78','88'])).

thf('90',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('91',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('95',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['94','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('102',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('103',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('104',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('105',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('106',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('107',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('108',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('113',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('114',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['111','120'])).

thf('122',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['91'])).

thf(t55_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( v3_pre_topc @ D @ B )
                       => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

thf('123',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X25 @ X24 @ X23 @ X22 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('126',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('128',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('130',plain,
    ( ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('132',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('133',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','133'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('135',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( zip_tseitin_0 @ B @ A )
               => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) )).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('139',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('142',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('143',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('144',plain,
    ( ( ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('146',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('147',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('148',plain,
    ( ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['119'])).

thf('150',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['136','150'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('156',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X17 ) @ X19 )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_1 @ X0 @ X2 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t105_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf('162',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( X39 != X37 )
      | ( v3_pre_topc @ X39 @ ( k6_tmap_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X38 @ X37 ) ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('163',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X38 @ X37 ) ) ) )
      | ( v3_pre_topc @ X37 @ ( k6_tmap_1 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['161','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['160','171'])).

thf('173',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','172'])).

thf('174',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('177',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['174','177'])).

thf('179',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('180',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['119'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('184',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('185',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('188',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 )
        = ( k10_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('195',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('197',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('198',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('199',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
          = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['186','187'])).

thf('202',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['119'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['191','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['182','205'])).

thf('207',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('208',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('209',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('210',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X5 @ X5 @ ( k6_partfun1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('211',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( k10_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      = sk_B )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['208','211'])).

thf('213',plain,
    ( ( ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
        = sk_B )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['207','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['186','187'])).

thf('215',plain,
    ( ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
      = sk_B )
   <= ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['119'])).

thf('217',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','206','217'])).

thf('219',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['111','120'])).

thf('220',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('222',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','220','221'])).

thf('223',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('225',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['186','187'])).

thf('227',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('229',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( zip_tseitin_0 @ X0 @ sk_A ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ X0 @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('232',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('234',plain,
    ( ( zip_tseitin_2 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['222','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_1 @ sk_B @ X1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['160','171'])).

thf('237',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B ) @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('239',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('240',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['182','205'])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('244',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('247',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 )
        = ( k10_relat_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 ) )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('249',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['215','216'])).

thf('250',plain,
    ( ( ( k10_relat_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ sk_B )
      = sk_B )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['237','238','239','247','250'])).

thf('252',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','251'])).

thf('253',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['91'])).

thf('254',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['89','254'])).

thf('256',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['115'])).

thf('257',plain,
    ( ( k7_tmap_1 @ sk_A @ sk_B )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['252'])).

thf('260',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['255','260'])).

thf('262',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('263',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('264',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relset_1 @ X5 @ X5 @ ( k6_partfun1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('265',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X17 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ X1 ) ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['267'])).

thf('269',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ X1 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X23 @ X24 ) @ X24 @ X23 @ X22 )
      | ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['262','272'])).

thf('274',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('275',plain,
    ( ~ ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('277',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('278',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('279',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('280',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('282',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['277','283'])).

thf('285',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('286',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('287',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('288',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['289'])).

thf('291',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( zip_tseitin_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['284','285','290','291'])).

thf('293',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['276','292'])).

thf('294',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('295',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('296',plain,(
    zip_tseitin_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','294','295'])).

thf('297',plain,(
    v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['275','296'])).

thf('298',plain,(
    $false ),
    inference(demod,[status(thm)],['261','297'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DQoIAp1xK8
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.96/4.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.96/4.17  % Solved by: fo/fo7.sh
% 3.96/4.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.96/4.17  % done 2475 iterations in 3.689s
% 3.96/4.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.96/4.17  % SZS output start Refutation
% 3.96/4.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.96/4.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.96/4.17  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 3.96/4.17  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.96/4.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.96/4.17  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.96/4.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.96/4.17  thf(sk_B_type, type, sk_B: $i).
% 3.96/4.17  thf(sk_A_type, type, sk_A: $i).
% 3.96/4.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.96/4.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.96/4.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.96/4.17  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 3.96/4.17  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 3.96/4.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.96/4.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 3.96/4.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.96/4.17  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 3.96/4.17  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.96/4.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.96/4.17  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.96/4.17  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.96/4.17  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.96/4.17  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 3.96/4.17  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.96/4.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.96/4.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.96/4.17  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.96/4.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.96/4.17  thf(t113_tmap_1, conjecture,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17           ( ( v3_pre_topc @ B @ A ) <=>
% 3.96/4.17             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.96/4.17               ( v1_funct_2 @
% 3.96/4.17                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.96/4.17                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.96/4.17               ( v5_pre_topc @
% 3.96/4.17                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 3.96/4.17               ( m1_subset_1 @
% 3.96/4.17                 ( k7_tmap_1 @ A @ B ) @ 
% 3.96/4.17                 ( k1_zfmisc_1 @
% 3.96/4.17                   ( k2_zfmisc_1 @
% 3.96/4.17                     ( u1_struct_0 @ A ) @ 
% 3.96/4.17                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf(zf_stmt_0, negated_conjecture,
% 3.96/4.17    (~( ![A:$i]:
% 3.96/4.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.96/4.17            ( l1_pre_topc @ A ) ) =>
% 3.96/4.17          ( ![B:$i]:
% 3.96/4.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17              ( ( v3_pre_topc @ B @ A ) <=>
% 3.96/4.17                ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.96/4.17                  ( v1_funct_2 @
% 3.96/4.17                    ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.96/4.17                    ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.96/4.17                  ( v5_pre_topc @
% 3.96/4.17                    ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 3.96/4.17                  ( m1_subset_1 @
% 3.96/4.17                    ( k7_tmap_1 @ A @ B ) @ 
% 3.96/4.17                    ( k1_zfmisc_1 @
% 3.96/4.17                      ( k2_zfmisc_1 @
% 3.96/4.17                        ( u1_struct_0 @ A ) @ 
% 3.96/4.17                        ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 3.96/4.17    inference('cnf.neg', [status(esa)], [t113_tmap_1])).
% 3.96/4.17  thf('0', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(dt_k7_tmap_1, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.96/4.17         ( l1_pre_topc @ A ) & 
% 3.96/4.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.96/4.17       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.96/4.17         ( v1_funct_2 @
% 3.96/4.17           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.96/4.17           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.96/4.17         ( m1_subset_1 @
% 3.96/4.17           ( k7_tmap_1 @ A @ B ) @ 
% 3.96/4.17           ( k1_zfmisc_1 @
% 3.96/4.17             ( k2_zfmisc_1 @
% 3.96/4.17               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.96/4.17  thf('1', plain,
% 3.96/4.17      (![X33 : $i, X34 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X33)
% 3.96/4.17          | ~ (v2_pre_topc @ X33)
% 3.96/4.17          | (v2_struct_0 @ X33)
% 3.96/4.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.96/4.17          | (m1_subset_1 @ (k7_tmap_1 @ X33 @ X34) @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ 
% 3.96/4.17               (u1_struct_0 @ (k6_tmap_1 @ X33 @ X34))))))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.96/4.17  thf('2', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 3.96/4.17        | (v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['0', '1'])).
% 3.96/4.17  thf('3', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(d10_tmap_1, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.96/4.17  thf('4', plain,
% 3.96/4.17      (![X29 : $i, X30 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.96/4.17          | ((k7_tmap_1 @ X30 @ X29) = (k6_partfun1 @ (u1_struct_0 @ X30)))
% 3.96/4.17          | ~ (l1_pre_topc @ X30)
% 3.96/4.17          | ~ (v2_pre_topc @ X30)
% 3.96/4.17          | (v2_struct_0 @ X30))),
% 3.96/4.17      inference('cnf', [status(esa)], [d10_tmap_1])).
% 3.96/4.17  thf('5', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['3', '4'])).
% 3.96/4.17  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('8', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('demod', [status(thm)], ['5', '6', '7'])).
% 3.96/4.17  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('10', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('11', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(t104_tmap_1, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 3.96/4.17             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 3.96/4.17  thf('12', plain,
% 3.96/4.17      (![X35 : $i, X36 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 3.96/4.17          | ((u1_struct_0 @ (k6_tmap_1 @ X36 @ X35)) = (u1_struct_0 @ X36))
% 3.96/4.17          | ~ (l1_pre_topc @ X36)
% 3.96/4.17          | ~ (v2_pre_topc @ X36)
% 3.96/4.17          | (v2_struct_0 @ X36))),
% 3.96/4.17      inference('cnf', [status(esa)], [t104_tmap_1])).
% 3.96/4.17  thf('13', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['11', '12'])).
% 3.96/4.17  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('16', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.96/4.17  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('18', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('21', plain,
% 3.96/4.17      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17        | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['2', '10', '18', '19', '20'])).
% 3.96/4.17  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('23', plain,
% 3.96/4.17      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k1_zfmisc_1 @ 
% 3.96/4.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('clc', [status(thm)], ['21', '22'])).
% 3.96/4.17  thf('24', plain,
% 3.96/4.17      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('25', plain,
% 3.96/4.17      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('split', [status(esa)], ['24'])).
% 3.96/4.17  thf('26', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(t106_tmap_1, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17           ( ( v3_pre_topc @ B @ A ) <=>
% 3.96/4.17             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 3.96/4.17               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 3.96/4.17  thf('27', plain,
% 3.96/4.17      (![X40 : $i, X41 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 3.96/4.17          | ~ (v3_pre_topc @ X40 @ X41)
% 3.96/4.17          | ((g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))
% 3.96/4.17              = (k6_tmap_1 @ X41 @ X40))
% 3.96/4.17          | ~ (l1_pre_topc @ X41)
% 3.96/4.17          | ~ (v2_pre_topc @ X41)
% 3.96/4.17          | (v2_struct_0 @ X41))),
% 3.96/4.17      inference('cnf', [status(esa)], [t106_tmap_1])).
% 3.96/4.17  thf('28', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17            = (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['26', '27'])).
% 3.96/4.17  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('31', plain,
% 3.96/4.17      (((v2_struct_0 @ sk_A)
% 3.96/4.17        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17            = (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['28', '29', '30'])).
% 3.96/4.17  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('33', plain,
% 3.96/4.17      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 3.96/4.17        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17            = (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('clc', [status(thm)], ['31', '32'])).
% 3.96/4.17  thf('34', plain,
% 3.96/4.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17          = (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['25', '33'])).
% 3.96/4.17  thf('35', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf(t62_pre_topc, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( ( v1_funct_1 @ C ) & 
% 3.96/4.17                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.96/4.17                 ( m1_subset_1 @
% 3.96/4.17                   C @ 
% 3.96/4.17                   ( k1_zfmisc_1 @
% 3.96/4.17                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.96/4.17               ( ![D:$i]:
% 3.96/4.17                 ( ( ( v1_funct_1 @ D ) & 
% 3.96/4.17                     ( v1_funct_2 @
% 3.96/4.17                       D @ 
% 3.96/4.17                       ( u1_struct_0 @
% 3.96/4.17                         ( g1_pre_topc @
% 3.96/4.17                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 3.96/4.17                       ( u1_struct_0 @ B ) ) & 
% 3.96/4.17                     ( m1_subset_1 @
% 3.96/4.17                       D @ 
% 3.96/4.17                       ( k1_zfmisc_1 @
% 3.96/4.17                         ( k2_zfmisc_1 @
% 3.96/4.17                           ( u1_struct_0 @
% 3.96/4.17                             ( g1_pre_topc @
% 3.96/4.17                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 3.96/4.17                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.96/4.17                   ( ( ( C ) = ( D ) ) =>
% 3.96/4.17                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.96/4.17                       ( v5_pre_topc @
% 3.96/4.17                         D @ 
% 3.96/4.17                         ( g1_pre_topc @
% 3.96/4.17                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 3.96/4.17                         B ) ) ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf('36', plain,
% 3.96/4.17      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.96/4.17         (~ (v2_pre_topc @ X8)
% 3.96/4.17          | ~ (l1_pre_topc @ X8)
% 3.96/4.17          | ~ (v1_funct_1 @ X9)
% 3.96/4.17          | ~ (v1_funct_2 @ X9 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))) @ 
% 3.96/4.17               (u1_struct_0 @ X8))
% 3.96/4.17          | ~ (m1_subset_1 @ X9 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ 
% 3.96/4.17                 (u1_struct_0 @ 
% 3.96/4.17                  (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))) @ 
% 3.96/4.17                 (u1_struct_0 @ X8))))
% 3.96/4.17          | ~ (v5_pre_topc @ X9 @ 
% 3.96/4.17               (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)) @ X8)
% 3.96/4.17          | (v5_pre_topc @ X11 @ X10 @ X8)
% 3.96/4.17          | ((X11) != (X9))
% 3.96/4.17          | ~ (m1_subset_1 @ X11 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 3.96/4.17          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 3.96/4.17          | ~ (v1_funct_1 @ X11)
% 3.96/4.17          | ~ (l1_pre_topc @ X10)
% 3.96/4.17          | ~ (v2_pre_topc @ X10))),
% 3.96/4.17      inference('cnf', [status(esa)], [t62_pre_topc])).
% 3.96/4.17  thf('37', plain,
% 3.96/4.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.96/4.17         (~ (v2_pre_topc @ X10)
% 3.96/4.17          | ~ (l1_pre_topc @ X10)
% 3.96/4.17          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 3.96/4.17          | ~ (m1_subset_1 @ X9 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 3.96/4.17          | (v5_pre_topc @ X9 @ X10 @ X8)
% 3.96/4.17          | ~ (v5_pre_topc @ X9 @ 
% 3.96/4.17               (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)) @ X8)
% 3.96/4.17          | ~ (m1_subset_1 @ X9 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ 
% 3.96/4.17                 (u1_struct_0 @ 
% 3.96/4.17                  (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))) @ 
% 3.96/4.17                 (u1_struct_0 @ X8))))
% 3.96/4.17          | ~ (v1_funct_2 @ X9 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))) @ 
% 3.96/4.17               (u1_struct_0 @ X8))
% 3.96/4.17          | ~ (v1_funct_1 @ X9)
% 3.96/4.17          | ~ (l1_pre_topc @ X8)
% 3.96/4.17          | ~ (v2_pre_topc @ X8))),
% 3.96/4.17      inference('simplify', [status(thm)], ['36'])).
% 3.96/4.17  thf('38', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X1 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 3.96/4.17               (u1_struct_0 @ sk_A))))
% 3.96/4.17          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (v1_funct_1 @ X1)
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 3.96/4.17               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17          | ~ (v5_pre_topc @ X1 @ 
% 3.96/4.17               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (m1_subset_1 @ X1 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ 
% 3.96/4.17               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17          | ~ (l1_pre_topc @ X0)
% 3.96/4.17          | ~ (v2_pre_topc @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['35', '37'])).
% 3.96/4.17  thf('39', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(dt_k6_tmap_1, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.96/4.17         ( l1_pre_topc @ A ) & 
% 3.96/4.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.96/4.17       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 3.96/4.17         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 3.96/4.17         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 3.96/4.17  thf('40', plain,
% 3.96/4.17      (![X31 : $i, X32 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X31)
% 3.96/4.17          | ~ (v2_pre_topc @ X31)
% 3.96/4.17          | (v2_struct_0 @ X31)
% 3.96/4.17          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.96/4.17          | (v2_pre_topc @ (k6_tmap_1 @ X31 @ X32)))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 3.96/4.17  thf('41', plain,
% 3.96/4.17      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['39', '40'])).
% 3.96/4.17  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('44', plain,
% 3.96/4.17      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.96/4.17  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('46', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['44', '45'])).
% 3.96/4.17  thf('47', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('48', plain,
% 3.96/4.17      (![X31 : $i, X32 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X31)
% 3.96/4.17          | ~ (v2_pre_topc @ X31)
% 3.96/4.17          | (v2_struct_0 @ X31)
% 3.96/4.17          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.96/4.17          | (l1_pre_topc @ (k6_tmap_1 @ X31 @ X32)))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 3.96/4.17  thf('49', plain,
% 3.96/4.17      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['47', '48'])).
% 3.96/4.17  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('52', plain,
% 3.96/4.17      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.96/4.17  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('54', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['52', '53'])).
% 3.96/4.17  thf('55', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('56', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('57', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('58', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X1 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 3.96/4.17               (u1_struct_0 @ sk_A))))
% 3.96/4.17          | ~ (v1_funct_1 @ X1)
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ 
% 3.96/4.17               (u1_struct_0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 3.96/4.17               (u1_struct_0 @ sk_A))
% 3.96/4.17          | ~ (v5_pre_topc @ X1 @ 
% 3.96/4.17               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | (v5_pre_topc @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (m1_subset_1 @ X1 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 3.96/4.17          | ~ (l1_pre_topc @ X0)
% 3.96/4.17          | ~ (v2_pre_topc @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['38', '46', '54', '55', '56', '57'])).
% 3.96/4.17  thf('59', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (m1_subset_1 @ X0 @ 
% 3.96/4.17              (k1_zfmisc_1 @ 
% 3.96/4.17               (k2_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 3.96/4.17                (u1_struct_0 @ sk_A))))
% 3.96/4.17           | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17           | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17           | ~ (m1_subset_1 @ X0 @ 
% 3.96/4.17                (k1_zfmisc_1 @ 
% 3.96/4.17                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | ~ (v5_pre_topc @ X0 @ 
% 3.96/4.17                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 3.96/4.17                (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | ~ (v1_funct_2 @ X0 @ 
% 3.96/4.17                (u1_struct_0 @ 
% 3.96/4.17                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 3.96/4.17                (u1_struct_0 @ sk_A))
% 3.96/4.17           | ~ (v1_funct_1 @ X0)))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['34', '58'])).
% 3.96/4.17  thf('60', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('63', plain,
% 3.96/4.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17          = (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['25', '33'])).
% 3.96/4.17  thf('64', plain,
% 3.96/4.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 3.96/4.17          = (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['25', '33'])).
% 3.96/4.17  thf('65', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('66', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (m1_subset_1 @ X0 @ 
% 3.96/4.17              (k1_zfmisc_1 @ 
% 3.96/4.17               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17           | ~ (m1_subset_1 @ X0 @ 
% 3.96/4.17                (k1_zfmisc_1 @ 
% 3.96/4.17                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17                (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17           | ~ (v1_funct_1 @ X0)))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)],
% 3.96/4.17                ['59', '60', '61', '62', '63', '64', '65'])).
% 3.96/4.17  thf('67', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (v1_funct_1 @ X0)
% 3.96/4.17           | ~ (v5_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17                (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | (v5_pre_topc @ X0 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17           | ~ (m1_subset_1 @ X0 @ 
% 3.96/4.17                (k1_zfmisc_1 @ 
% 3.96/4.17                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('simplify', [status(thm)], ['66'])).
% 3.96/4.17  thf('68', plain,
% 3.96/4.17      (((~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17         | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17            (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17         | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['23', '67'])).
% 3.96/4.17  thf('69', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('70', plain,
% 3.96/4.17      (![X33 : $i, X34 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X33)
% 3.96/4.17          | ~ (v2_pre_topc @ X33)
% 3.96/4.17          | (v2_struct_0 @ X33)
% 3.96/4.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.96/4.17          | (v1_funct_2 @ (k7_tmap_1 @ X33 @ X34) @ (u1_struct_0 @ X33) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ X33 @ X34))))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.96/4.17  thf('71', plain,
% 3.96/4.17      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17        | (v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['69', '70'])).
% 3.96/4.17  thf('72', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('73', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('76', plain,
% 3.96/4.17      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17        | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 3.96/4.17  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('78', plain,
% 3.96/4.17      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['76', '77'])).
% 3.96/4.17  thf('79', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('80', plain,
% 3.96/4.17      (![X33 : $i, X34 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X33)
% 3.96/4.17          | ~ (v2_pre_topc @ X33)
% 3.96/4.17          | (v2_struct_0 @ X33)
% 3.96/4.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.96/4.17          | (v1_funct_1 @ (k7_tmap_1 @ X33 @ X34)))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.96/4.17  thf('81', plain,
% 3.96/4.17      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v2_struct_0 @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['79', '80'])).
% 3.96/4.17  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('84', plain,
% 3.96/4.17      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.96/4.17  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('86', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['84', '85'])).
% 3.96/4.17  thf('87', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('88', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)], ['86', '87'])).
% 3.96/4.17  thf('89', plain,
% 3.96/4.17      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17          (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 3.96/4.17         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)], ['68', '78', '88'])).
% 3.96/4.17  thf('90', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('91', plain,
% 3.96/4.17      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('92', plain,
% 3.96/4.17      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('split', [status(esa)], ['91'])).
% 3.96/4.17  thf('93', plain,
% 3.96/4.17      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['90', '92'])).
% 3.96/4.17  thf('94', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('95', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('96', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 3.96/4.17        | (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('97', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('split', [status(esa)], ['96'])).
% 3.96/4.17  thf('98', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['95', '97'])).
% 3.96/4.17  thf('99', plain,
% 3.96/4.17      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['94', '98'])).
% 3.96/4.17  thf('100', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 3.96/4.17        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('101', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('102', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('103', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('104', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('105', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('106', plain,
% 3.96/4.17      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['76', '77'])).
% 3.96/4.17  thf('107', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('108', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)], ['86', '87'])).
% 3.96/4.17  thf('109', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)],
% 3.96/4.17                ['100', '101', '102', '103', '104', '105', '106', '107', '108'])).
% 3.96/4.17  thf('110', plain,
% 3.96/4.17      (((~ (v3_pre_topc @ sk_B @ sk_A)
% 3.96/4.17         | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['99', '109'])).
% 3.96/4.17  thf('111', plain,
% 3.96/4.17      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))) & 
% 3.96/4.17             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['93', '110'])).
% 3.96/4.17  thf('112', plain,
% 3.96/4.17      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k1_zfmisc_1 @ 
% 3.96/4.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('clc', [status(thm)], ['21', '22'])).
% 3.96/4.17  thf('113', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('114', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('115', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 3.96/4.17        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('116', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 3.96/4.17         <= (~
% 3.96/4.17             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('split', [status(esa)], ['115'])).
% 3.96/4.17  thf('117', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (~
% 3.96/4.17             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['114', '116'])).
% 3.96/4.17  thf('118', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k1_zfmisc_1 @ 
% 3.96/4.17            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (~
% 3.96/4.17             ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['113', '117'])).
% 3.96/4.17  thf('119', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['112', '118'])).
% 3.96/4.17  thf('120', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['119'])).
% 3.96/4.17  thf('121', plain,
% 3.96/4.17      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['111', '120'])).
% 3.96/4.17  thf('122', plain,
% 3.96/4.17      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('split', [status(esa)], ['91'])).
% 3.96/4.17  thf(t55_tops_2, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( l1_pre_topc @ A ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( l1_pre_topc @ B ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( ( m1_subset_1 @
% 3.96/4.17                   C @ 
% 3.96/4.17                   ( k1_zfmisc_1 @
% 3.96/4.17                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 3.96/4.17                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.96/4.17                 ( v1_funct_1 @ C ) ) =>
% 3.96/4.17               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.96/4.17                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.96/4.17                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.96/4.17                   ( ![D:$i]:
% 3.96/4.17                     ( ( m1_subset_1 @
% 3.96/4.17                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.96/4.17                       ( ( v3_pre_topc @ D @ B ) =>
% 3.96/4.17                         ( v3_pre_topc @
% 3.96/4.17                           ( k8_relset_1 @
% 3.96/4.17                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.96/4.17                           A ) ) ) ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf(zf_stmt_1, axiom,
% 3.96/4.17    (![C:$i,B:$i,A:$i]:
% 3.96/4.17     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 3.96/4.17       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 3.96/4.17         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 3.96/4.17  thf('123', plain,
% 3.96/4.17      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 3.96/4.17         (~ (v5_pre_topc @ X24 @ X22 @ X23)
% 3.96/4.17          | (zip_tseitin_1 @ X25 @ X24 @ X23 @ X22)
% 3.96/4.17          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.96/4.17  thf('124', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17           | (zip_tseitin_1 @ X0 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['122', '123'])).
% 3.96/4.17  thf('125', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('126', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('127', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['124', '125', '126'])).
% 3.96/4.17  thf(d3_struct_0, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.96/4.17  thf('128', plain,
% 3.96/4.17      (![X6 : $i]:
% 3.96/4.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.96/4.17  thf('129', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('130', plain,
% 3.96/4.17      ((((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 3.96/4.17        | ~ (l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('sup+', [status(thm)], ['128', '129'])).
% 3.96/4.17  thf('131', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['52', '53'])).
% 3.96/4.17  thf(dt_l1_pre_topc, axiom,
% 3.96/4.17    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.96/4.17  thf('132', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.96/4.17  thf('133', plain, ((l1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('sup-', [status(thm)], ['131', '132'])).
% 3.96/4.17  thf('134', plain,
% 3.96/4.17      (((k2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['130', '133'])).
% 3.96/4.17  thf(zf_stmt_2, axiom,
% 3.96/4.17    (![B:$i,A:$i]:
% 3.96/4.17     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 3.96/4.17         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.96/4.17       ( zip_tseitin_0 @ B @ A ) ))).
% 3.96/4.17  thf('135', plain,
% 3.96/4.17      (![X15 : $i, X16 : $i]:
% 3.96/4.17         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X15) = (k1_xboole_0)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.96/4.17  thf('136', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 3.96/4.17          | (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 3.96/4.17      inference('sup+', [status(thm)], ['134', '135'])).
% 3.96/4.17  thf('137', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('split', [status(esa)], ['96'])).
% 3.96/4.17  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.96/4.17  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 3.96/4.17  thf(zf_stmt_5, axiom,
% 3.96/4.17    (![D:$i,C:$i,B:$i,A:$i]:
% 3.96/4.17     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 3.96/4.17       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.96/4.17         ( ( v3_pre_topc @ D @ B ) =>
% 3.96/4.17           ( v3_pre_topc @
% 3.96/4.17             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 3.96/4.17             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 3.96/4.17  thf(zf_stmt_7, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( l1_pre_topc @ A ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( l1_pre_topc @ B ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( ( v1_funct_1 @ C ) & 
% 3.96/4.17                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.96/4.17                 ( m1_subset_1 @
% 3.96/4.17                   C @ 
% 3.96/4.17                   ( k1_zfmisc_1 @
% 3.96/4.17                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.96/4.17               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 3.96/4.17  thf('138', plain,
% 3.96/4.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X26)
% 3.96/4.17          | ~ (zip_tseitin_0 @ X26 @ X27)
% 3.96/4.17          | (zip_tseitin_2 @ X28 @ X26 @ X27)
% 3.96/4.17          | ~ (m1_subset_1 @ X28 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 3.96/4.17          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 3.96/4.17          | ~ (v1_funct_1 @ X28)
% 3.96/4.17          | ~ (l1_pre_topc @ X27))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.96/4.17  thf('139', plain,
% 3.96/4.17      (((~ (l1_pre_topc @ sk_A)
% 3.96/4.17         | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['137', '138'])).
% 3.96/4.17  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('141', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['84', '85'])).
% 3.96/4.17  thf('142', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('143', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['52', '53'])).
% 3.96/4.17  thf('144', plain,
% 3.96/4.17      (((~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (u1_struct_0 @ sk_A))
% 3.96/4.17         | (zip_tseitin_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17            (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 3.96/4.17  thf('145', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('146', plain,
% 3.96/4.17      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['76', '77'])).
% 3.96/4.17  thf('147', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('148', plain,
% 3.96/4.17      ((((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17          (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17         | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 3.96/4.17  thf('149', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['119'])).
% 3.96/4.17  thf('150', plain,
% 3.96/4.17      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 3.96/4.17  thf('151', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 3.96/4.17        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['136', '150'])).
% 3.96/4.17  thf('152', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['124', '125', '126'])).
% 3.96/4.17  thf('153', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 3.96/4.17           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['151', '152'])).
% 3.96/4.17  thf('154', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('155', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('156', plain,
% 3.96/4.17      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.96/4.17          | (v3_pre_topc @ 
% 3.96/4.17             (k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20 @ 
% 3.96/4.17              X17) @ 
% 3.96/4.17             X19)
% 3.96/4.17          | ~ (v3_pre_topc @ X17 @ X18)
% 3.96/4.17          | ~ (zip_tseitin_1 @ X17 @ X20 @ X18 @ X19))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.96/4.17  thf('157', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 3.96/4.17          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | (v3_pre_topc @ 
% 3.96/4.17             (k8_relset_1 @ (u1_struct_0 @ X1) @ 
% 3.96/4.17              (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0) @ 
% 3.96/4.17             X1))),
% 3.96/4.17      inference('sup-', [status(thm)], ['155', '156'])).
% 3.96/4.17  thf('158', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('159', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | ~ (zip_tseitin_1 @ X0 @ X2 @ (k6_tmap_1 @ sk_A @ sk_B) @ X1)
% 3.96/4.17          | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | (v3_pre_topc @ 
% 3.96/4.17             (k8_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_A) @ X2 @ X0) @ 
% 3.96/4.17             X1))),
% 3.96/4.17      inference('demod', [status(thm)], ['157', '158'])).
% 3.96/4.17  thf('160', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         ((v3_pre_topc @ 
% 3.96/4.17           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 3.96/4.17           X0)
% 3.96/4.17          | ~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['154', '159'])).
% 3.96/4.17  thf('161', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf(t105_tmap_1, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( m1_subset_1 @
% 3.96/4.17                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 3.96/4.17               ( ( ( C ) = ( B ) ) =>
% 3.96/4.17                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf('162', plain,
% 3.96/4.17      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.96/4.17          | ((X39) != (X37))
% 3.96/4.17          | (v3_pre_topc @ X39 @ (k6_tmap_1 @ X38 @ X37))
% 3.96/4.17          | ~ (m1_subset_1 @ X39 @ 
% 3.96/4.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X38 @ X37))))
% 3.96/4.17          | ~ (l1_pre_topc @ X38)
% 3.96/4.17          | ~ (v2_pre_topc @ X38)
% 3.96/4.17          | (v2_struct_0 @ X38))),
% 3.96/4.17      inference('cnf', [status(esa)], [t105_tmap_1])).
% 3.96/4.17  thf('163', plain,
% 3.96/4.17      (![X37 : $i, X38 : $i]:
% 3.96/4.17         ((v2_struct_0 @ X38)
% 3.96/4.17          | ~ (v2_pre_topc @ X38)
% 3.96/4.17          | ~ (l1_pre_topc @ X38)
% 3.96/4.17          | ~ (m1_subset_1 @ X37 @ 
% 3.96/4.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X38 @ X37))))
% 3.96/4.17          | (v3_pre_topc @ X37 @ (k6_tmap_1 @ X38 @ X37))
% 3.96/4.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 3.96/4.17      inference('simplify', [status(thm)], ['162'])).
% 3.96/4.17  thf('164', plain,
% 3.96/4.17      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17        | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17        | ~ (v2_pre_topc @ sk_A)
% 3.96/4.17        | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('sup-', [status(thm)], ['161', '163'])).
% 3.96/4.17  thf('165', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('166', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('169', plain,
% 3.96/4.17      (((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.96/4.17      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 3.96/4.17  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('171', plain, ((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['169', '170'])).
% 3.96/4.17  thf('172', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         ((v3_pre_topc @ 
% 3.96/4.17           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 3.96/4.17           X0)
% 3.96/4.17          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['160', '171'])).
% 3.96/4.17  thf('173', plain,
% 3.96/4.17      (((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 3.96/4.17         | (v3_pre_topc @ 
% 3.96/4.17            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 3.96/4.17            sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['153', '172'])).
% 3.96/4.17  thf('174', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('175', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['95', '97'])).
% 3.96/4.17  thf(redefinition_k8_relset_1, axiom,
% 3.96/4.17    (![A:$i,B:$i,C:$i,D:$i]:
% 3.96/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.96/4.17       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.96/4.17  thf('176', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.96/4.17          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 3.96/4.17      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.96/4.17  thf('177', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['175', '176'])).
% 3.96/4.17  thf('178', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['174', '177'])).
% 3.96/4.17  thf('179', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('180', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['178', '179'])).
% 3.96/4.17  thf('181', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['119'])).
% 3.96/4.17  thf('182', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['180', '181'])).
% 3.96/4.17  thf('183', plain,
% 3.96/4.17      (![X6 : $i]:
% 3.96/4.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.96/4.17  thf('184', plain,
% 3.96/4.17      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k1_zfmisc_1 @ 
% 3.96/4.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('clc', [status(thm)], ['21', '22'])).
% 3.96/4.17  thf('185', plain,
% 3.96/4.17      (((m1_subset_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17        | ~ (l1_struct_0 @ sk_A))),
% 3.96/4.17      inference('sup+', [status(thm)], ['183', '184'])).
% 3.96/4.17  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('187', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 3.96/4.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.96/4.17  thf('188', plain, ((l1_struct_0 @ sk_A)),
% 3.96/4.17      inference('sup-', [status(thm)], ['186', '187'])).
% 3.96/4.17  thf('189', plain,
% 3.96/4.17      ((m1_subset_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k1_zfmisc_1 @ 
% 3.96/4.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('demod', [status(thm)], ['185', '188'])).
% 3.96/4.17  thf('190', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.96/4.17          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 3.96/4.17      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.96/4.17  thf('191', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['189', '190'])).
% 3.96/4.17  thf('192', plain,
% 3.96/4.17      (![X6 : $i]:
% 3.96/4.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.96/4.17  thf('193', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('split', [status(esa)], ['96'])).
% 3.96/4.17  thf('194', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.96/4.17          | ((k8_relset_1 @ X1 @ X2 @ X0 @ X3) = (k10_relat_1 @ X0 @ X3)))),
% 3.96/4.17      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.96/4.17  thf('195', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 3.96/4.17            (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['193', '194'])).
% 3.96/4.17  thf('196', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('197', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('198', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('199', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 3.96/4.17  thf('200', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17             (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 3.96/4.17             = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))
% 3.96/4.17           | ~ (l1_struct_0 @ sk_A)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['192', '199'])).
% 3.96/4.17  thf('201', plain, ((l1_struct_0 @ sk_A)),
% 3.96/4.17      inference('sup-', [status(thm)], ['186', '187'])).
% 3.96/4.17  thf('202', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['200', '201'])).
% 3.96/4.17  thf('203', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['119'])).
% 3.96/4.17  thf('204', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['202', '203'])).
% 3.96/4.17  thf('205', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('sup+', [status(thm)], ['191', '204'])).
% 3.96/4.17  thf('206', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['182', '205'])).
% 3.96/4.17  thf('207', plain,
% 3.96/4.17      (![X6 : $i]:
% 3.96/4.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.96/4.17  thf('208', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 3.96/4.17  thf('209', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(t171_funct_2, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.96/4.17       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 3.96/4.17  thf('210', plain,
% 3.96/4.17      (![X4 : $i, X5 : $i]:
% 3.96/4.17         (((k8_relset_1 @ X5 @ X5 @ (k6_partfun1 @ X5) @ X4) = (X4))
% 3.96/4.17          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 3.96/4.17      inference('cnf', [status(esa)], [t171_funct_2])).
% 3.96/4.17  thf('211', plain,
% 3.96/4.17      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 3.96/4.17      inference('sup-', [status(thm)], ['209', '210'])).
% 3.96/4.17  thf('212', plain,
% 3.96/4.17      ((((k10_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) = (sk_B)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['208', '211'])).
% 3.96/4.17  thf('213', plain,
% 3.96/4.17      (((((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))
% 3.96/4.17         | ~ (l1_struct_0 @ sk_A)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['207', '212'])).
% 3.96/4.17  thf('214', plain, ((l1_struct_0 @ sk_A)),
% 3.96/4.17      inference('sup-', [status(thm)], ['186', '187'])).
% 3.96/4.17  thf('215', plain,
% 3.96/4.17      ((((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B)))
% 3.96/4.17         <= (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17                 (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))))),
% 3.96/4.17      inference('demod', [status(thm)], ['213', '214'])).
% 3.96/4.17  thf('216', plain,
% 3.96/4.17      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17         (k1_zfmisc_1 @ 
% 3.96/4.17          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['119'])).
% 3.96/4.17  thf('217', plain,
% 3.96/4.17      (((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['215', '216'])).
% 3.96/4.17  thf('218', plain,
% 3.96/4.17      (((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v3_pre_topc @ sk_B @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['173', '206', '217'])).
% 3.96/4.17  thf('219', plain,
% 3.96/4.17      ((~ (v3_pre_topc @ sk_B @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['111', '120'])).
% 3.96/4.17  thf('220', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('221', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('222', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (~ (zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17           | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 3.96/4.17              (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['127', '220', '221'])).
% 3.96/4.17  thf('223', plain,
% 3.96/4.17      (![X6 : $i]:
% 3.96/4.17         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.96/4.17  thf('224', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('225', plain,
% 3.96/4.17      (((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['223', '224'])).
% 3.96/4.17  thf('226', plain, ((l1_struct_0 @ sk_A)),
% 3.96/4.17      inference('sup-', [status(thm)], ['186', '187'])).
% 3.96/4.17  thf('227', plain,
% 3.96/4.17      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['225', '226'])).
% 3.96/4.17  thf('228', plain,
% 3.96/4.17      (![X15 : $i, X16 : $i]:
% 3.96/4.17         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X16) != (k1_xboole_0)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.96/4.17  thf('229', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ sk_A)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['227', '228'])).
% 3.96/4.17  thf('230', plain,
% 3.96/4.17      ((![X0 : $i]: (zip_tseitin_0 @ X0 @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('simplify', [status(thm)], ['229'])).
% 3.96/4.17  thf('231', plain,
% 3.96/4.17      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 3.96/4.17        | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 3.96/4.17  thf('232', plain,
% 3.96/4.17      (((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['230', '231'])).
% 3.96/4.17  thf('233', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('234', plain,
% 3.96/4.17      (((zip_tseitin_2 @ (k6_partfun1 @ k1_xboole_0) @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['232', '233'])).
% 3.96/4.17  thf('235', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          (zip_tseitin_1 @ X0 @ (k6_partfun1 @ k1_xboole_0) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['222', '234'])).
% 3.96/4.17  thf('236', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         ((v3_pre_topc @ 
% 3.96/4.17           (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ sk_B) @ 
% 3.96/4.17           X0)
% 3.96/4.17          | ~ (zip_tseitin_1 @ sk_B @ X1 @ (k6_tmap_1 @ sk_A @ sk_B) @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['160', '171'])).
% 3.96/4.17  thf('237', plain,
% 3.96/4.17      (((v3_pre_topc @ 
% 3.96/4.17         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17          (k6_partfun1 @ k1_xboole_0) @ sk_B) @ 
% 3.96/4.17         sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['235', '236'])).
% 3.96/4.17  thf('238', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('239', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('240', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('241', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.96/4.17           = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['182', '205'])).
% 3.96/4.17  thf('242', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17            (k6_partfun1 @ k1_xboole_0) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['240', '241'])).
% 3.96/4.17  thf('243', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('244', plain,
% 3.96/4.17      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('clc', [status(thm)], ['218', '219'])).
% 3.96/4.17  thf('245', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.96/4.17            (k6_partfun1 @ k1_xboole_0) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ X0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['242', '243', '244'])).
% 3.96/4.17  thf('246', plain,
% 3.96/4.17      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['225', '226'])).
% 3.96/4.17  thf('247', plain,
% 3.96/4.17      ((![X0 : $i]:
% 3.96/4.17          ((k8_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.96/4.17            (k6_partfun1 @ k1_xboole_0) @ X0)
% 3.96/4.17            = (k10_relat_1 @ (k6_partfun1 @ k1_xboole_0) @ X0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['245', '246'])).
% 3.96/4.17  thf('248', plain,
% 3.96/4.17      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['225', '226'])).
% 3.96/4.17  thf('249', plain,
% 3.96/4.17      (((k10_relat_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)) @ sk_B) = (sk_B))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['215', '216'])).
% 3.96/4.17  thf('250', plain,
% 3.96/4.17      ((((k10_relat_1 @ (k6_partfun1 @ k1_xboole_0) @ sk_B) = (sk_B)))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('sup+', [status(thm)], ['248', '249'])).
% 3.96/4.17  thf('251', plain,
% 3.96/4.17      (((v3_pre_topc @ sk_B @ sk_A))
% 3.96/4.17         <= (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['237', '238', '239', '247', '250'])).
% 3.96/4.17  thf('252', plain,
% 3.96/4.17      (~
% 3.96/4.17       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('demod', [status(thm)], ['121', '251'])).
% 3.96/4.17  thf('253', plain,
% 3.96/4.17      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 3.96/4.17       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('split', [status(esa)], ['91'])).
% 3.96/4.17  thf('254', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['252', '253'])).
% 3.96/4.17  thf('255', plain,
% 3.96/4.17      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['89', '254'])).
% 3.96/4.17  thf('256', plain,
% 3.96/4.17      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (~
% 3.96/4.17             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('split', [status(esa)], ['115'])).
% 3.96/4.17  thf('257', plain,
% 3.96/4.17      (((k7_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('clc', [status(thm)], ['8', '9'])).
% 3.96/4.17  thf('258', plain,
% 3.96/4.17      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17         <= (~
% 3.96/4.17             ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))))),
% 3.96/4.17      inference('demod', [status(thm)], ['256', '257'])).
% 3.96/4.17  thf('259', plain,
% 3.96/4.17      (~
% 3.96/4.17       ((v5_pre_topc @ (k7_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 3.96/4.17         (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('sat_resolution*', [status(thm)], ['252'])).
% 3.96/4.17  thf('260', plain,
% 3.96/4.17      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 3.96/4.17          (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 3.96/4.17  thf('261', plain,
% 3.96/4.17      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17          (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['255', '260'])).
% 3.96/4.17  thf('262', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('263', plain,
% 3.96/4.17      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 3.96/4.17         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21)
% 3.96/4.17          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.96/4.17  thf('264', plain,
% 3.96/4.17      (![X4 : $i, X5 : $i]:
% 3.96/4.17         (((k8_relset_1 @ X5 @ X5 @ (k6_partfun1 @ X5) @ X4) = (X4))
% 3.96/4.17          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 3.96/4.17      inference('cnf', [status(esa)], [t171_funct_2])).
% 3.96/4.17  thf('265', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.96/4.17         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 3.96/4.17          | ((k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 3.96/4.17              (k6_partfun1 @ (u1_struct_0 @ X0)) @ X1) = (X1)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['263', '264'])).
% 3.96/4.17  thf('266', plain,
% 3.96/4.17      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 3.96/4.17         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21)
% 3.96/4.17          | ~ (v3_pre_topc @ 
% 3.96/4.17               (k8_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 3.96/4.17                X20 @ X17) @ 
% 3.96/4.17               X21))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.96/4.17  thf('267', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.96/4.17         (~ (v3_pre_topc @ X0 @ X1)
% 3.96/4.17          | (zip_tseitin_1 @ X0 @ X3 @ X1 @ X2)
% 3.96/4.17          | (zip_tseitin_1 @ X0 @ (k6_partfun1 @ (u1_struct_0 @ X1)) @ X1 @ X1))),
% 3.96/4.17      inference('sup-', [status(thm)], ['265', '266'])).
% 3.96/4.17  thf('268', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (v3_pre_topc @ X1 @ X0)
% 3.96/4.17          | (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 3.96/4.17      inference('condensation', [status(thm)], ['267'])).
% 3.96/4.17  thf('269', plain,
% 3.96/4.17      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 3.96/4.17         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21) | (v3_pre_topc @ X17 @ X18))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.96/4.17  thf('270', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (zip_tseitin_1 @ X1 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)),
% 3.96/4.17      inference('clc', [status(thm)], ['268', '269'])).
% 3.96/4.17  thf('271', plain,
% 3.96/4.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.96/4.17         (~ (zip_tseitin_1 @ (sk_D @ X22 @ X23 @ X24) @ X24 @ X23 @ X22)
% 3.96/4.17          | (v5_pre_topc @ X24 @ X22 @ X23)
% 3.96/4.17          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.96/4.17  thf('272', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         (~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0)
% 3.96/4.17          | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ X0)) @ X0 @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['270', '271'])).
% 3.96/4.17  thf('273', plain,
% 3.96/4.17      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v5_pre_topc @ 
% 3.96/4.17           (k6_partfun1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['262', '272'])).
% 3.96/4.17  thf('274', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('275', plain,
% 3.96/4.17      ((~ (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('demod', [status(thm)], ['273', '274'])).
% 3.96/4.17  thf('276', plain,
% 3.96/4.17      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k1_zfmisc_1 @ 
% 3.96/4.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('clc', [status(thm)], ['21', '22'])).
% 3.96/4.17  thf('277', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('278', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('279', plain,
% 3.96/4.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.96/4.17         (~ (l1_pre_topc @ X26)
% 3.96/4.17          | ~ (zip_tseitin_0 @ X26 @ X27)
% 3.96/4.17          | (zip_tseitin_2 @ X28 @ X26 @ X27)
% 3.96/4.17          | ~ (m1_subset_1 @ X28 @ 
% 3.96/4.17               (k1_zfmisc_1 @ 
% 3.96/4.17                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 3.96/4.17          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 3.96/4.17          | ~ (v1_funct_1 @ X28)
% 3.96/4.17          | ~ (l1_pre_topc @ X27))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.96/4.17  thf('280', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X1 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 3.96/4.17          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (v1_funct_1 @ X1)
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) @ 
% 3.96/4.17               (u1_struct_0 @ X0))
% 3.96/4.17          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (l1_pre_topc @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['278', '279'])).
% 3.96/4.17  thf('281', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['52', '53'])).
% 3.96/4.17  thf('282', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('283', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X1 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 3.96/4.17          | ~ (v1_funct_1 @ X1)
% 3.96/4.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.96/4.17          | (zip_tseitin_2 @ X1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (zip_tseitin_0 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (l1_pre_topc @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['280', '281', '282'])).
% 3.96/4.17  thf('284', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (zip_tseitin_0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17               (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 3.96/4.17               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 3.96/4.17          | ~ (v1_funct_1 @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['277', '283'])).
% 3.96/4.17  thf('285', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('clc', [status(thm)], ['52', '53'])).
% 3.96/4.17  thf('286', plain,
% 3.96/4.17      (![X15 : $i, X16 : $i]:
% 3.96/4.17         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X15) = (k1_xboole_0)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.96/4.17  thf('287', plain,
% 3.96/4.17      (![X15 : $i, X16 : $i]:
% 3.96/4.17         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X16) != (k1_xboole_0)))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.96/4.17  thf('288', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.17         (((k1_xboole_0) != (k1_xboole_0))
% 3.96/4.17          | (zip_tseitin_0 @ X0 @ X2)
% 3.96/4.17          | (zip_tseitin_0 @ X1 @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['286', '287'])).
% 3.96/4.17  thf('289', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.96/4.17         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.96/4.17      inference('simplify', [status(thm)], ['288'])).
% 3.96/4.17  thf('290', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 3.96/4.17      inference('eq_fact', [status(thm)], ['289'])).
% 3.96/4.17  thf('291', plain,
% 3.96/4.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['16', '17'])).
% 3.96/4.17  thf('292', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         (~ (m1_subset_1 @ X0 @ 
% 3.96/4.17             (k1_zfmisc_1 @ 
% 3.96/4.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.96/4.17          | (zip_tseitin_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 3.96/4.17             (k6_tmap_1 @ sk_A @ sk_B))
% 3.96/4.17          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17          | ~ (v1_funct_1 @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['284', '285', '290', '291'])).
% 3.96/4.17  thf('293', plain,
% 3.96/4.17      ((~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.96/4.17        | (zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17           (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 3.96/4.17      inference('sup-', [status(thm)], ['276', '292'])).
% 3.96/4.17  thf('294', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('demod', [status(thm)], ['86', '87'])).
% 3.96/4.17  thf('295', plain,
% 3.96/4.17      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.96/4.17      inference('clc', [status(thm)], ['76', '77'])).
% 3.96/4.17  thf('296', plain,
% 3.96/4.17      ((zip_tseitin_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('demod', [status(thm)], ['293', '294', '295'])).
% 3.96/4.17  thf('297', plain,
% 3.96/4.17      ((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 3.96/4.17        (k6_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 3.96/4.17      inference('demod', [status(thm)], ['275', '296'])).
% 3.96/4.17  thf('298', plain, ($false), inference('demod', [status(thm)], ['261', '297'])).
% 3.96/4.17  
% 3.96/4.17  % SZS output end Refutation
% 3.96/4.17  
% 3.96/4.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
